use emacs::{defun, Env, Result, Value, IntoLisp};
use rusqlite::{Connection, params};
use std::fs;
use std::path::Path;
use std::time::Duration;
use walkdir::WalkDir;
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};
// Use org-rs (org_element) as requested
use org_element::parser::{Parser, ParseGranularity};
use org_element::environment::DefaultEnvironment;

emacs::plugin_is_GPL_compatible!();

#[emacs::module(name = "org-roam-sync-rs")]
fn init(env: &Env) -> Result<()> {
    env.message("org-roam-sync-rs (with org-rs/org_element) loaded successfully!")?;
    Ok(())
}

#[derive(Debug)]
struct FileInfo {
    path: String,
    hash: String,
    content: String,
}

#[derive(Debug)]
pub struct Node {
    id: String,
    file: String,
    level: i64,
    pos: i64,
    todo: Option<String>,
    priority: Option<String>,
    title: String,
    properties: String,
    olp: String,
}

#[derive(Debug)]
pub struct Tag {
    node_id: String,
    tag: String,
}

#[derive(Debug)]
pub struct Alias {
    node_id: String,
    alias: String,
}

fn compute_hash(content: &str) -> String {
    use sha1::{Sha1, Digest};
    let mut hasher = Sha1::new();
    hasher.update(content.as_bytes());
    format!("{:x}", hasher.finalize())
}

fn get_org_files(dir: &str) -> Vec<String> {
    WalkDir::new(dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("org"))
        // Skip Emacs transient files: auto-save (#name#), lock (.#name), backup (name~).
        // A lock file such as `.#foo.org` still has extension "org", so filter by name too.
        .filter(|e| {
            e.path()
                .file_name()
                .and_then(|s| s.to_str())
                .map(|n| !(n.starts_with('#') || n.starts_with(".#") || n.ends_with('~')))
                .unwrap_or(false)
        })
        .map(|e| e.path().to_string_lossy().into_owned())
        .collect()
}

use std::rc::Rc;
use org_element::data::{Syntax, SyntaxNode};

fn lisp_str(s: &str) -> String {
    format!("\"{}\"", s.escape_debug())
}



fn format_properties(props: &HashMap<String, String>) -> String {
    if props.is_empty() {
        return "nil".to_string();
    }
    let mut pairs = Vec::new();
    for (k, v) in props {
        pairs.push(format!("({} . {})", lisp_str(k), lisp_str(v)));
    }
    format!("({})", pairs.join(" "))
}

fn format_olp(olp: &[String]) -> String {
    if olp.is_empty() {
        "nil".to_string()
    } else {
        let escaped: Vec<String> = olp.iter().map(|s| lisp_str(s)).collect();
        format!("({})", escaped.join(" "))
    }
}

use std::sync::LazyLock;

static RE_TITLE: LazyLock<regex::Regex> = LazyLock::new(|| regex::Regex::new(r"(?im)^[ \t]*#\+TITLE:[ \t]*(.*)").unwrap());
static RE_DRAWER: LazyLock<regex::Regex> = LazyLock::new(|| regex::Regex::new(r"(?im)^[ \t]*:PROPERTIES:[ \t]*\n([\s\S]*?)\n[ \t]*:END:[ \t]*").unwrap());
static RE_PROP: LazyLock<regex::Regex> = LazyLock::new(|| regex::Regex::new(r"(?im)^[ \t]*:([a-zA-Z0-9_$-]+):[ \t]*(.*)").unwrap());
static RE_FILETAGS: LazyLock<regex::Regex> = LazyLock::new(|| regex::Regex::new(r"(?im)^[ \t]*#\+(?:FILETAGS|ROAM_TAGS):[ \t]*(.*)").unwrap());
static RE_ROAM_ALIASES: LazyLock<regex::Regex> = LazyLock::new(|| regex::Regex::new(r"(?im)^[ \t]*#\+(?:ROAM_ALIASES):[ \t]*(.*)").unwrap());
// Start of any Org headline line (one or more leading stars followed by a space).
static RE_HEADLINE: LazyLock<regex::Regex> = LazyLock::new(|| regex::Regex::new(r"(?m)^\*+[ \t]").unwrap());

fn extract_title(text: &str) -> String {
    if let Some(caps) = RE_TITLE.captures(text) {
        caps.get(1).unwrap().as_str().trim().to_string()
    } else {
        "".to_string()
    }
}

fn extract_properties(text: &str) -> HashMap<String, String> {
    let mut props = HashMap::new();
    if let Some(caps) = RE_DRAWER.captures(text) {
        let props_text = caps.get(1).unwrap().as_str();
        for p_caps in RE_PROP.captures_iter(props_text) {
            props.insert(p_caps.get(1).unwrap().as_str().to_uppercase(), p_caps.get(2).unwrap().as_str().to_string());
        }
    }
    props
}

fn walk_ast<'a>(
    node: Rc<SyntaxNode<'a>>,
    current_olp: &mut Vec<String>,
    nodes: &mut Vec<Node>,
    tags: &mut Vec<Tag>,
    aliases: &mut Vec<Alias>,
    file_path: &str,
    content: &str,
    file_title: &str,
) {
    let mut pushed_olp = false;

    // File-level node
    if let Syntax::OrgData = node.data {
        let mut first_headline_start = content.len();
        for child in node.children.borrow().iter() {
            if let Syntax::Headline(_) = child.data {
                first_headline_start = child.location.start;
                break;
            }
        }
        let text_to_scan = &content[0..first_headline_start];

        let props = extract_properties(text_to_scan);
        if let Some(node_id) = props.get("ID") {
            let final_title = if file_title.is_empty() {
                Path::new(file_path).file_stem().unwrap().to_string_lossy().to_string()
            } else {
                file_title.to_string()
            };

            nodes.push(Node {
                id: lisp_str(node_id),
                file: lisp_str(file_path),
                level: 0,
                pos: 1,
                todo: Some("nil".to_string()),
                priority: Some("nil".to_string()),
                title: lisp_str(&final_title),
                properties: format_properties(&props),
                olp: "nil".to_string(),
            });
            if let Some(aliases_str) = props.get("ROAM_ALIASES") {
                aliases.push(Alias { node_id: lisp_str(node_id), alias: lisp_str(aliases_str) });
            }
            if let Some(caps) = RE_ROAM_ALIASES.captures(text_to_scan) {
                let alias_str = caps.get(1).unwrap().as_str().trim();
                for alias in alias_str.split_whitespace() {
                    if !alias.trim().is_empty() {
                        aliases.push(Alias { node_id: lisp_str(node_id), alias: lisp_str(alias.trim()) });
                    }
                }
            }

            if let Some(caps) = RE_FILETAGS.captures(text_to_scan) {
                let tag_str = caps.get(1).unwrap().as_str().trim();
                for tag in tag_str.split(':') {
                    if !tag.trim().is_empty() {
                        tags.push(Tag { node_id: lisp_str(node_id), tag: lisp_str(tag.trim()) });
                    }
                }
            }
        }
    }

    // Headline node
    if let Syntax::Headline(ref data) = node.data {
        let title = data.title.to_string();
        current_olp.push(title.clone());
        pushed_olp = true;

        // Bound the property scan to THIS heading's own content: from the heading
        // line up to the next headline of any level. org-rs reports a leaf heading's
        // `location.end` as extending past following siblings, so relying on it (or on
        // the first *child* headline) lets an ID-less heading swallow a sibling's
        // `:PROPERTIES:` drawer, producing a duplicate node id. Search the raw text
        // for the next `^\*+ ` after this heading's own line instead.
        let start = node.location.start;
        let line_end = content[start..]
            .find('\n')
            .map(|i| start + i + 1)
            .unwrap_or(content.len());
        let scan_end = RE_HEADLINE
            .find(&content[line_end..])
            .map(|m| line_end + m.start())
            .unwrap_or(content.len());
        let text_to_scan = &content[start..scan_end];
        let props = extract_properties(text_to_scan);

        if let Some(node_id) = props.get("ID") {
            nodes.push(Node {
                id: lisp_str(node_id),
                file: lisp_str(file_path),
                level: data.level as i64,
                pos: node.location.start as i64 + 1,
                todo: Some("nil".to_string()),
                priority: Some("nil".to_string()),
                title: lisp_str(&title),
                properties: format_properties(&props),
                olp: format_olp(&current_olp[..current_olp.len()-1]),
            });

            if let Some(aliases_str) = props.get("ROAM_ALIASES") {
                aliases.push(Alias { node_id: lisp_str(node_id), alias: lisp_str(aliases_str) });
            }

            for tag_ref in &data.tags {
                tags.push(Tag { node_id: lisp_str(node_id), tag: lisp_str(&tag_ref.0.to_string()) });
            }
        }
    }

    for child in node.children.borrow().iter() {
        walk_ast(Rc::clone(child), current_olp, nodes, tags, aliases, file_path, content, file_title);
    }

    if pushed_olp {
        current_olp.pop();
    }
}

pub fn parse_org_file(file: &str, content: &str) -> (Vec<Node>, Vec<Tag>, Vec<Alias>, String) {
    let mut nodes = Vec::new();
    let mut tags = Vec::new();
    let mut aliases = Vec::new();

    // org-rs API usage
    let parser = Parser::new(content, ParseGranularity::Element, DefaultEnvironment);
    let ast = parser.parse_buffer();

    let file_title = extract_title(content);

    let mut current_olp = Vec::new();
    walk_ast(Rc::new(ast), &mut current_olp, &mut nodes, &mut tags, &mut aliases, file, content, &file_title);

    (nodes, tags, aliases, file_title)
}

#[defun]
fn sync_db<'e>(env: &'e Env, roam_dir: String, db_path: String, force: Value<'e>) -> Result<Value<'e>> {
    env.message(&format!("Starting org-rs powered org-roam DB sync for {}", roam_dir))?;

    let force_bool = force.is_not_nil();
    if force_bool && Path::new(&db_path).exists() {
        fs::remove_file(&db_path).unwrap_or_default();
    }

    // Open the DB and wait (rather than instantly failing) when another connection
    // — a running Emacs org-roam session, a second daemon, or an interrupted sync —
    // still holds the lock. Without busy_timeout, a transient "database is locked"
    // used to panic on `.unwrap()` and abort the whole Emacs init.
    let mut conn = Connection::open(&db_path)
        .map_err(|e| emacs::Error::msg(format!("org-roam-sync-rs: cannot open {}: {}", db_path, e)))?;
    conn.busy_timeout(Duration::from_secs(10))
        .map_err(|e| emacs::Error::msg(format!("org-roam-sync-rs: busy_timeout failed: {}", e)))?;

    conn.pragma_update(None, "user_version", 20)
        .map_err(|e| emacs::Error::msg(format!("org-roam-sync-rs: DB is locked/busy ({}); another Emacs or sync may be holding {}", e, db_path)))?;
    conn.execute_batch("
        PRAGMA foreign_keys = ON;
        PRAGMA synchronous = OFF;
        PRAGMA journal_mode = MEMORY;
        PRAGMA temp_store = MEMORY;
        CREATE TABLE IF NOT EXISTS files (file UNIQUE PRIMARY KEY, title, hash NOT NULL, atime NOT NULL, mtime NOT NULL);
        CREATE TABLE IF NOT EXISTS nodes (id NOT NULL PRIMARY KEY, file NOT NULL, level NOT NULL, pos NOT NULL, todo, priority, scheduled text, deadline text, title, properties, olp, FOREIGN KEY (file) REFERENCES files (file) ON DELETE CASCADE);
        CREATE TABLE IF NOT EXISTS aliases (node_id NOT NULL, alias, FOREIGN KEY (node_id) REFERENCES nodes (id) ON DELETE CASCADE);
        CREATE TABLE IF NOT EXISTS citations (node_id NOT NULL, cite_key NOT NULL, pos NOT NULL, properties, FOREIGN KEY (node_id) REFERENCES nodes (id) ON DELETE CASCADE);
        CREATE TABLE IF NOT EXISTS refs (node_id NOT NULL, ref NOT NULL, type NOT NULL, FOREIGN KEY (node_id) REFERENCES nodes (id) ON DELETE CASCADE);
        CREATE TABLE IF NOT EXISTS tags (node_id NOT NULL, tag, FOREIGN KEY (node_id) REFERENCES nodes (id) ON DELETE CASCADE);
        CREATE TABLE IF NOT EXISTS links (pos NOT NULL, source NOT NULL, dest NOT NULL, type NOT NULL, properties NOT NULL, FOREIGN KEY (source) REFERENCES nodes (id) ON DELETE CASCADE);
    ").map_err(|e| emacs::Error::msg(format!("org-roam-sync-rs: schema init failed (DB busy?): {}", e)))?;

    let mut current_files: HashMap<String, String> = HashMap::new();
    {
        let mut stmt = conn.prepare("SELECT file, hash FROM files").unwrap();
        let mut rows = stmt.query([]).unwrap();
        while let Some(row) = rows.next().unwrap() {
            let mut file: String = row.get(0).unwrap();
            if file.starts_with('"') && file.ends_with('"') {
                file = file[1..file.len()-1].to_string();
            }
            let mut hash: String = row.get(1).unwrap();
            if hash.starts_with('"') && hash.ends_with('"') {
                hash = hash[1..hash.len()-1].to_string();
            }
            current_files.insert(file, hash);
        }
    }

    let org_files = get_org_files(&roam_dir);
    
    let processed_files: Vec<FileInfo> = org_files.into_par_iter().filter_map(|path| {
        if let Ok(content) = fs::read_to_string(&path) {
            Some(FileInfo { path, hash: compute_hash(&content), content })
        } else { None }
    }).collect();

    let mut modified_files = Vec::new();
    let mut current_keys: HashSet<String> = current_files.keys().cloned().collect();

    for file_info in &processed_files {
        current_keys.remove(&file_info.path);
        let mut is_modified = true;
        if let Some(db_hash) = current_files.get(&file_info.path) {
            if *db_hash == file_info.hash { is_modified = false; }
        }
        if is_modified { modified_files.push(file_info); }
    }

    let removed_files: Vec<String> = current_keys.into_iter().collect();
    let modified_count = modified_files.len();

    let tx = conn.transaction()
        .map_err(|e| emacs::Error::msg(format!("org-roam-sync-rs: begin transaction failed (DB busy?): {}", e)))?;

    for file in &removed_files {
        let l_file = lisp_str(file);
        tx.execute("DELETE FROM files WHERE file = ?", params![l_file]).unwrap();
        tx.execute("DELETE FROM nodes WHERE file = ?", params![l_file]).unwrap();
    }

    let all_new_nodes: Vec<(String, String, Vec<Node>, Vec<Tag>, Vec<Alias>, String)> = modified_files.into_par_iter()
        .map(|f| {
            let (nodes, tags, aliases, title) = parse_org_file(&f.path, &f.content);
            (f.path.clone(), f.hash.clone(), nodes, tags, aliases, title)
        })
        .collect();

    // Track node IDs inserted during this run so a duplicate `:ID:` (e.g. a copied
    // note, or a stale row left by an interrupted sync) can never abort the whole
    // Emacs daemon via a panicking UNIQUE-constraint unwrap. `INSERT OR REPLACE`
    // makes last-writer-win; we still count collisions to surface them to the user.
    let mut seen_ids: HashSet<String> = HashSet::new();
    let mut dup_ids: usize = 0;

    for (path, hash, nodes, tags, aliases, file_title) in all_new_nodes {
        let l_path = lisp_str(&path);
        let l_hash = lisp_str(&hash);
        let final_title = if file_title.is_empty() {
            Path::new(&path).file_stem().unwrap().to_string_lossy().to_string()
        } else {
            file_title.clone()
        };
        tx.execute("DELETE FROM files WHERE file = ?", params![&l_path]).unwrap();
        tx.execute("DELETE FROM nodes WHERE file = ?", params![&l_path]).unwrap();
        tx.execute("INSERT INTO files (file, title, hash, atime, mtime) VALUES (?, ?, ?, ?, ?)", params![&l_path, lisp_str(&final_title), &l_hash, "(0 0 0 0)", "(0 0 0 0)"]).unwrap();

        for node in nodes {
            if !seen_ids.insert(node.id.clone()) {
                dup_ids += 1;
                eprintln!(
                    "org-roam-sync-rs: duplicate node id {} in {} — replacing previous occurrence",
                    node.id, path
                );
            }
            if let Err(e) = tx.execute(
                "INSERT OR REPLACE INTO nodes (id, file, level, pos, todo, priority, title, properties, olp) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                params![node.id, node.file, node.level, node.pos, node.todo, node.priority, node.title, node.properties, node.olp],
            ) {
                eprintln!("org-roam-sync-rs: failed to insert node {} ({}): {}", node.id, path, e);
                continue;
            }
        }

        for tag in tags {
            if let Err(e) = tx.execute("INSERT INTO tags (node_id, tag) VALUES (?, ?)", params![tag.node_id, tag.tag]) {
                eprintln!("org-roam-sync-rs: failed to insert tag for {}: {}", tag.node_id, e);
            }
        }

        for alias in aliases {
            if let Err(e) = tx.execute("INSERT INTO aliases (node_id, alias) VALUES (?, ?)", params![alias.node_id, alias.alias]) {
                eprintln!("org-roam-sync-rs: failed to insert alias for {}: {}", alias.node_id, e);
            }
        }
    }

    tx.commit()
        .map_err(|e| emacs::Error::msg(format!("org-roam-sync-rs: commit failed (DB busy?): {}", e)))?;

    let msg = if dup_ids > 0 {
        format!(
            "Rust Sync Complete using org-rs: removed {}, modified {} ({} duplicate node id(s) replaced)",
            removed_files.len(), modified_count, dup_ids
        )
    } else {
        format!("Rust Sync Complete using org-rs: removed {}, modified {}", removed_files.len(), modified_count)
    };
    env.message(&msg)?;

    msg.into_lisp(env)
}

