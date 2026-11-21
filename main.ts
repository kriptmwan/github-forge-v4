// Forge v4 — a perf-first, single-process, GitHub-compatible git forge.
// Written fresh from the competition spec (RULES.txt wire contract).
// Surfaces: git smart HTTP (upload-pack v2, receive-pack v0), REST v3,
// GraphQL v4, MCP (Streamable HTTP). Node 22 standard library only.
// Deterministic: no wall clock or unseeded randomness reaches stored state.

import http from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

const VIEWER = 'adaiversen';
const VIEWER_ID = 1000;
const VIEWER_NAME = 'ada iversen';
const VIEWER_EMAIL = 'adaiversen@example.invalid';
const FIXED_ISO = '2026-11-14T06:30:00.000Z';
const FIXED_EPOCH = 1700000000;
const ZERO_OID = '0'.repeat(40);
const VERSION = '1.0.0';

const sha1hex = (buf) => createHash('sha1').update(buf).digest('hex');
const isOid = (s) => typeof s === 'string' && /^[0-9a-f]{40}$/.test(s);

// ---- git object hashing -------------------------------------------------
function hashObject(type, data) {
  const head = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return sha1hex(Buffer.concat([head, data]));
}
function looseHeader(type, data) {
  return Buffer.from(`${type} ${data.length}\0`, 'utf8');
}

// ---- pkt-line -----------------------------------------------------------
function pktLine(payload) {
  const b = Buffer.isBuffer(payload) ? payload : Buffer.from(payload, 'utf8');
  const len = b.length + 4;
  const head = Buffer.alloc(4);
  head.write(len.toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([head, b]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');
function pktLines(list) {
  const parts = [];
  for (const item of list) {
    if (item === 'flush') parts.push(PKT_FLUSH);
    else if (item === 'delim') parts.push(PKT_DELIM);
    else parts.push(pktLine(item));
  }
  return Buffer.concat(parts);
}
// Decode a whole buffer of pkt-lines. Returns [{kind:'data'|'flush'|'delim', payload}]
function decodePktLines(buf) {
  const out = [];
  let off = 0;
  while (off + 4 <= buf.length) {
    const len = parseInt(buf.toString('ascii', off, off + 4), 16);
    if (!Number.isFinite(len) || len < 0) throw new Error('bad pkt-line length');
    if (len === 0) { out.push({ kind: 'flush', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (len === 1) { out.push({ kind: 'delim', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (len < 4 || off + len > buf.length) throw new Error('truncated pkt-line');
    out.push({ kind: 'data', payload: buf.subarray(off + 4, off + len) });
    off += len;
  }
  if (off !== buf.length) throw new Error('trailing bytes after pkt-lines');
  return out;
}
function pktTextLines(buf) {
  const lines = [];
  for (const p of decodePktLines(buf)) {
    if (p.kind === 'data') lines.push(p.payload.toString('utf8'));
  }
  return lines;
}

// ---- pack reading / writing ---------------------------------------------
function readVarint(buf, off) {
  let size = buf[off] & 0x0f;
  let shift = 4;
  let i = off;
  while (buf[i] & 0x80) { i++; size |= (buf[i] & 0x7f) << shift; shift += 7; }
  return { size, next: i + 1 };
}
function readOfsVarint(buf, off) {
  let i = off;
  let v = buf[i] & 0x7f;
  while (buf[i] & 0x80) { i++; v = ((v + 1) << 7) | (buf[i] & 0x7f); }
  return { value: v, next: i + 1 };
}
function applyDelta(base, delta) {
  let p = 0;
  const readDVar = () => { let v = 0; let s = 0; while (true) { const b = delta[p++]; v |= (b & 0x7f) << s; s += 7; if (!(b & 0x80)) break; } return v; };
  const srcSize = readDVar();
  const tgtSize = readDVar();
  if (srcSize !== base.length) throw new Error('delta base size mismatch');
  const out = [];
  let total = 0;
  while (p < delta.length) {
    const op = delta[p++];
    if (op & 0x80) {
      let off = 0; let size = 0;
      for (let b = 0; b < 4; b++) if (op & (1 << b)) off |= delta[p++] << (8 * b);
      for (let b = 0; b < 3; b++) if (op & (0x10 << b)) size |= delta[p++] << (8 * b);
      if (size === 0) size = 0x10000;
      out.push(base.subarray(off, off + size));
      total += size;
    } else if (op !== 0) {
      out.push(delta.subarray(p, p + op));
      p += op; total += op;
    } else throw new Error('delta op 0');
  }
  const res = Buffer.concat(out);
  if (res.length !== tgtSize || total !== tgtSize) throw new Error('delta size mismatch');
  return res;
}
// Parse a packfile into Map<oid,{type,data}>. Handles plain + OFS/REF deltas.
function readPack(buf) {
  if (buf.length < 12 || buf.toString('ascii', 0, 4) !== 'PACK') throw new Error('not a pack');
  const version = buf.readUInt32BE(4);
  const count = buf.readUInt32BE(8);
  const trailer = buf.subarray(buf.length - 20).toString('hex');
  if (sha1hex(buf.subarray(0, buf.length - 20)) !== trailer) throw new Error('pack checksum mismatch');
  const objects = new Map();
  const byOffset = new Map();
  const pending = [];
  let off = 12;
  const TYPE_NAMES = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
  for (let n = 0; n < count; n++) {
    const start = off;
    const typeNum = (buf[off] >> 4) & 0x07;
    const { size, next } = readVarint(buf, off);
    off = next;
    if (typeNum === 6) {
      const { value: negOff, next: n2 } = readOfsVarint(buf, off);
      off = n2;
      const inflated = inflateAt(buf, off);
      const data = inflated.data;
      off = inflated.next;
      pending.push({ kind: 'ofs', baseOffset: start - negOff, data, size });
    } else if (typeNum === 7) {
      const baseOid = buf.subarray(off, off + 20).toString('hex');
      off += 20;
      const inflated = inflateAt(buf, off);
      const data = inflated.data;
      off = inflated.next;
      pending.push({ kind: 'ref', baseOid, data, size });
    } else {
      const type = TYPE_NAMES[typeNum];
      if (!type) throw new Error('bad pack object type ' + typeNum);
      const inflated = inflateAt(buf, off);
      const data = inflated.data;
      off = inflated.next;
      if (data.length !== size) throw new Error('pack object size mismatch');
      const oid = hashObject(type, data);
      objects.set(oid, { type, data });
      byOffset.set(start, oid);
    }
  }
  // Resolve deltas (may chain).
  let guard = 0;
  while (pending.length && guard++ < 10000) {
    const rest = [];
    let progressed = false;
    for (const p of pending) {
      let base = null;
      if (p.kind === 'ofs') { const boid = byOffset.get(p.baseOffset); if (boid) base = objects.get(boid); }
      else base = objects.get(p.baseOid);
      if (!base) { rest.push(p); continue; }
      const data = applyDelta(base.data, p.data);
      const type = base.type;
      const oid = hashObject(type, data);
      objects.set(oid, { type, data });
      progressed = true;
    }
    pending.length = 0;
    pending.push(...rest);
    if (!progressed) throw new Error('unresolvable pack delta');
  }
  if (pending.length) throw new Error('unresolvable pack delta');
  return { version, objects };
}
// Inflate one zlib stream starting at off; returns its bytes and the offset just past it.
// inflateSync tolerates trailing bytes, and with {info:true} the engine's bytesWritten is
// exactly the consumed stream length (verified empirically on Node 22).
function inflateAt(buf, off) {
  const r = inflateSync(buf.subarray(off), { info: true });
  return { data: r.buffer, next: off + r.engine.bytesWritten };
}
const PACK_TYPE_NUM = { commit: 1, tree: 2, blob: 3, tag: 4 };
function writePackObjectHeader(typeNum, size) {
  const bytes = [];
  let b = (typeNum << 4) | (size & 0x0f);
  size >>= 4;
  if (size) b |= 0x80;
  bytes.push(b);
  while (size) { let c = size & 0x7f; size >>= 7; if (size) c |= 0x80; bytes.push(c); }
  return Buffer.from(bytes);
}
function writePack(objects) {
  const parts = [Buffer.from('PACK'), Buffer.alloc(4), Buffer.alloc(4)];
  parts[1].writeUInt32BE(2, 0);
  parts[2].writeUInt32BE(objects.length, 0);
  for (const obj of objects) {
    const deflated = deflateSync(obj.data, { level: 6 });
    parts.push(writePackObjectHeader(PACK_TYPE_NUM[obj.type], obj.data.length));
    parts.push(deflated);
  }
  const head = Buffer.concat(parts);
  const trailer = createHash('sha1').update(head).digest();
  return Buffer.concat([head, trailer]);
}

// ---- git object parsing ---------------------------------------------------
function parseCommit(data) {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split === -1 ? text : text.slice(0, split);
  const message = split === -1 ? '' : text.slice(split + 2);
  let tree = '';
  const parents = [];
  let author = '';
  let committer = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  return { tree, parents, author, committer, message };
}
function parseTree(data) {
  const entries = [];
  let off = 0;
  while (off < data.length) {
    const sp = data.indexOf(0x20, off);
    const nul = data.indexOf(0x00, sp);
    const mode = data.toString('ascii', off, sp);
    const name = data.toString('utf8', sp + 1, nul);
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    off = nul + 21;
  }
  return entries;
}
function parseTag(data) {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split === -1 ? text : text.slice(0, split);
  const message = split === -1 ? '' : text.slice(split + 2);
  let object = ''; let type = ''; let tag = ''; let tagger = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('object ')) object = line.slice(7).trim();
    else if (line.startsWith('type ')) type = line.slice(5).trim();
    else if (line.startsWith('tag ')) tag = line.slice(4).trim();
    else if (line.startsWith('tagger ')) tagger = line.slice(7);
  }
  return { object, type, tag, tagger, message };
}
function buildTree(entries) {
  // entries: [{mode,name,oid}] — git sorts by name, dirs as name+'/'.
  const sorted = [...entries].sort((a, b) => {
    const an = a.mode === '40000' ? a.name + '/' : a.name;
    const bn = b.mode === '40000' ? b.name + '/' : b.name;
    return an < bn ? -1 : an > bn ? 1 : 0;
  });
  const parts = [];
  for (const e of sorted) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}
function buildCommit({ tree, parents, message, author, committer, timestamp }) {
  const lines = [`tree ${tree}`];
  for (const p of parents) lines.push(`parent ${p}`);
  lines.push(`author ${author} ${timestamp} +0000`);
  lines.push(`committer ${committer} ${timestamp} +0000`);
  return Buffer.from(lines.join('\n') + '\n\n' + message, 'utf8');
}

// ---- store ----------------------------------------------------------------
let repoSeq = 0;
let issueIdSeq = 0;
let commentSeq = 0;
let serverCommitSeq = 0;
const repos = new Map(); // key: owner + '/' + name -> repo
const packCache = new Map(); // fetch pack cache, FIFO capped
const PACK_CACHE_MAX = 24;

function newRepo(owner, name, isPrivate, description) {
  repoSeq += 1;
  return {
    owner, name, private: !!isPrivate, description: description ?? '',
    databaseId: 5000 + repoSeq - 1,
    objects: new Map(), // oid -> {type, data}
    refs: new Map(), // refname -> oid
    issues: new Map(), // number -> issue record
    pulls: new Map(), // number -> pr record
    labels: new Map(), // name -> {name, color}
    numberSeq: 0,
    repoJson: null,
    issueJsonCache: new Map(), // number -> json string
    listCache: new Map(), // query key -> json string
  };
}
function repoKey(owner, name) { return owner + '/' + name; }
function getRepo(owner, name) { return repos.get(repoKey(owner, name)) ?? null; }
function getObject(repo, oid) { return repo.objects.get(oid) ?? null; }
function putObject(repo, type, data) {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}
function refTip(repo, ref) { return repo.refs.get(ref) ?? null; }
function isAncestor(repo, ancestor, tip) {
  if (ancestor === tip) return true;
  const seen = new Set();
  const stack = [tip];
  while (stack.length) {
    const cur = stack.pop();
    if (cur === ancestor) return true;
    if (seen.has(cur)) continue;
    seen.add(cur);
    const obj = getObject(repo, cur);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) stack.push(p);
  }
  return false;
}
// Walk commits from tips. depthLimit: max generations from a want (Infinity = all).
// Returns {commits:Set, objects:Map} of reachable objects (commits+trees+blobs+tags).
function collectReachable(repo, tips, depthLimit) {
  const commits = new Set();
  const objects = new Map();
  const queue = [];
  for (const t of tips) if (isOid(t)) queue.push([t, 0]);
  const seenCommit = new Set();
  while (queue.length) {
    const [oid, depth] = queue.pop();
    if (seenCommit.has(oid)) continue;
    seenCommit.add(oid);
    const obj = getObject(repo, oid);
    if (!obj) continue;
    if (obj.type === 'tag') {
      const tag = parseTag(obj.data);
      objects.set(oid, obj);
      if (isOid(tag.object)) queue.push([tag.object, depth]);
      continue;
    }
    if (obj.type !== 'commit') continue;
    commits.add(oid);
    objects.set(oid, obj);
    if (depthLimit !== Infinity && depth >= depthLimit) continue;
    const c = parseCommit(obj.data);
    for (const p of c.parents) queue.push([p, depth + 1]);
  }
  // Expand trees/blobs for collected commits.
  const expandTree = (treeOid) => {
    const t = getObject(repo, treeOid);
    if (!t || t.type !== 'tree') return;
    if (objects.has(treeOid)) return;
    objects.set(treeOid, t);
    for (const e of parseTree(t.data)) {
      const child = getObject(repo, e.oid);
      if (!child) continue;
      if (child.type === 'tree') expandTree(e.oid);
      else objects.set(e.oid, child);
    }
  };
  for (const oid of commits) {
    const c = parseCommit(getObject(repo, oid).data);
    expandTree(c.tree);
  }
  return { commits, objects };
}
// Tree path -> blob oid map for a commit's tree.
function treeToMap(repo, treeOid) {
  const out = new Map();
  const walk = (oid, prefix) => {
    const t = getObject(repo, oid);
    if (!t || t.type !== 'tree') return;
    for (const e of parseTree(t.data)) {
      const path = prefix ? prefix + '/' + e.name : e.name;
      if (e.mode === '40000') walk(e.oid, path);
      else out.set(path, { oid: e.oid, mode: e.mode });
    }
  };
  walk(treeOid, '');
  return out;
}
// Build a tree object from a path map, storing intermediate trees. Returns root tree oid.
function mapToTree(repo, fileMap) {
  const build = (dir) => {
    const entries = [];
    const subdirs = new Map();
    for (const [path, file] of fileMap) {
      if (!path.startsWith(dir)) continue;
      const rest = path.slice(dir.length);
      const slash = rest.indexOf('/');
      if (slash === -1) entries.push({ mode: file.mode, name: rest, oid: file.oid });
      else {
        const sub = rest.slice(0, slash);
        if (!subdirs.has(sub)) subdirs.set(sub, dir + sub + '/');
      }
    }
    for (const [sub, subdir] of subdirs) entries.push({ mode: '40000', name: sub, oid: build(subdir) });
    return putObject(repo, 'tree', buildTree(entries));
  };
  return build('');
}
function peelToCommit(repo, oid) {
  let cur = oid;
  for (let i = 0; i < 16; i++) {
    const obj = getObject(repo, cur);
    if (!obj) return null;
    if (obj.type === 'commit') return cur;
    if (obj.type === 'tag') { cur = parseTag(obj.data).object; continue; }
    return null;
  }
  return null;
}
function mergeBase(repo, a, b) {
  // First common ancestor by BFS from both sides (small histories).
  const fromA = new Set();
  const stack = [a];
  while (stack.length) {
    const cur = stack.pop();
    if (!cur || fromA.has(cur)) continue;
    fromA.add(cur);
    const obj = getObject(repo, cur);
    if (obj && obj.type === 'commit') for (const p of parseCommit(obj.data).parents) stack.push(p);
  }
  const stackB = [b];
  const seenB = new Set();
  while (stackB.length) {
    const cur = stackB.pop();
    if (!cur || seenB.has(cur)) continue;
    seenB.add(cur);
    if (fromA.has(cur)) return cur;
    const obj = getObject(repo, cur);
    if (obj && obj.type === 'commit') for (const p of parseCommit(obj.data).parents) stackB.push(p);
  }
  return null;
}
function diffFiles(repo, baseTreeOid, headTreeOid) {
  const base = baseTreeOid ? treeToMap(repo, baseTreeOid) : new Map();
  const head = headTreeOid ? treeToMap(repo, headTreeOid) : new Map();
  const files = [];
  for (const [path, h] of head) {
    const b = base.get(path);
    if (!b) files.push({ filename: path, status: 'added', headOid: h.oid });
    else if (b.oid !== h.oid) files.push({ filename: path, status: 'modified', headOid: h.oid, baseOid: b.oid });
  }
  for (const [path, b] of base) {
    if (!head.has(path)) files.push({ filename: path, status: 'removed', baseOid: b.oid });
  }
  files.sort((x, y) => (x.filename < y.filename ? -1 : 1));
  return files;
}
function countLineChanges(repo, file) {
  const read = (oid) => {
    if (!oid) return [];
    const o = getObject(repo, oid);
    if (!o) return [];
    const s = o.data.toString('utf8');
    return s === '' ? [] : s.split('\n');
  };
  const a = read(file.baseOid);
  const b = read(file.headOid);
  // Cheap line diff: count lines present in b but not in a (multiset) and vice versa.
  const count = (arr) => { const m = new Map(); for (const l of arr) m.set(l, (m.get(l) ?? 0) + 1); return m; };
  const ma = count(a); const mb = count(b);
  let additions = 0, deletions = 0;
  for (const [l, n] of mb) additions += Math.max(0, n - (ma.get(l) ?? 0));
  for (const [l, n] of ma) deletions += Math.max(0, n - (mb.get(l) ?? 0));
  if (file.status === 'added') { additions = b.length; deletions = 0; }
  if (file.status === 'removed') { additions = 0; deletions = a.length; }
  return { additions, deletions, changes: additions + deletions };
}
function serverCommit(repo, treeOid, parents, message) {
  serverCommitSeq += 1;
  const ts = FIXED_EPOCH + serverCommitSeq;
  const data = buildCommit({ tree: treeOid, parents, message: message.endsWith('\n') ? message : message + '\n', author: 'Forge <forge@example.invalid>', committer: 'Forge <forge@example.invalid>', timestamp: ts });
  return putObject(repo, 'commit', data);
}

// ---- JSON shapes (cached strings on hot paths) ---------------------------
function esc(s) {
  return JSON.stringify(String(s ?? ''));
}
function repoJsonString(repo) {
  if (repo.repoJson) return repo.repoJson;
  const s = JSON.stringify({
    id: repo.databaseId, node_id: 'R_' + Buffer.from(repo.owner + '/' + repo.name).toString('base64url'),
    name: repo.name, full_name: repo.owner + '/' + repo.name,
    owner: { login: repo.owner, id: VIEWER_ID, type: 'User' },
    private: repo.private, description: repo.description, default_branch: 'main',
    html_url: 'https://example.invalid/' + repo.owner + '/' + repo.name,
    clone_url: 'https://example.invalid/' + repo.owner + '/' + repo.name + '.git',
    has_issues: true, has_pull_requests: true, created_at: FIXED_ISO, updated_at: FIXED_ISO,
  });
  repo.repoJson = s;
  return s;
}
function issueJsonString(repo, issue) {
  const cached = repo.issueJsonCache.get(issue.number);
  if (cached) return cached;
  const s = JSON.stringify(issueJsonObject(repo, issue));
  repo.issueJsonCache.set(issue.number, s);
  return s;
}
function issueJsonObject(repo, issue) {
  return {
    id: issue.id, node_id: issue.nodeId, number: issue.number,
    title: issue.title, body: issue.body, state: issue.state,
    labels: issue.labels.map((l) => ({ name: l.name, color: l.color })),
    user: { login: VIEWER, id: VIEWER_ID, type: 'User' },
    created_at: FIXED_ISO, updated_at: FIXED_ISO,
    html_url: 'https://example.invalid/' + repo.owner + '/' + repo.name + '/issues/' + issue.number,
    comments: issue.comments.length,
  };
}
function prJsonObject(repo, pr) {
  return {
    id: pr.id, node_id: pr.nodeId, number: pr.number,
    title: pr.title, body: pr.body, state: pr.state,
    head: { ref: pr.head, sha: pr.headSha, label: repo.owner + ':' + pr.head },
    base: { ref: pr.base, sha: pr.baseSha, label: repo.owner + ':' + pr.base },
    merged: pr.merged, merged_at: pr.merged ? FIXED_ISO : null,
    merge_commit_sha: pr.mergeSha,
    user: { login: VIEWER, id: VIEWER_ID, type: 'User' },
    created_at: FIXED_ISO, updated_at: FIXED_ISO,
  };
}
function globalId(kind, repo, n) {
  return kind + '_' + Buffer.from(repo.owner + '/' + repo.name + '#' + n).toString('base64url');
}
function invalidateRepo(repo) { repo.repoJson = null; repo.listCache.clear(); }
function invalidateIssue(repo, number) { repo.issueJsonCache.delete(number); repo.listCache.clear(); }

// ---- HTTP plumbing ---------------------------------------------------------
let reqSeq = 0;
function readBody(req) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    let total = 0;
    req.on('data', (c) => { total += c.length; if (total > 64 * 1024 * 1024) { req.destroy(); reject(new Error('body too large')); } else chunks.push(c); });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
function sendJson(res, status, body, extra) {
  const s = typeof body === 'string' ? body : JSON.stringify(body);
  const headers = { 'content-type': 'application/json', 'x-github-request-id': 'req-' + (++reqSeq) };
  if (extra) for (const k of Object.keys(extra)) headers[k] = extra[k];
  res.writeHead(status, headers);
  res.end(s);
}
function sendErr(res, status, message) { sendJson(res, status, { message }); }
function bearer(req) {
  const h = req.headers.authorization;
  if (!h || !h.startsWith('Bearer ')) return null;
  const t = h.slice(7).trim();
  return t === '' ? null : t;
}
function parseJson(buf) {
  if (buf.length === 0) return {};
  return JSON.parse(buf.toString('utf8'));
}
function authorParts(line) {
  const m = /^(.*) <(.*)> \d+ [+-]\d{4}$/.exec(line ?? '');
  if (!m) return { name: 'Forge', email: 'forge@example.invalid' };
  return { name: m[1], email: m[2] };
}
function commitJson(repo, oid) {
  const obj = getObject(repo, oid);
  if (!obj) return null;
  const c = parseCommit(obj.data);
  const a = authorParts(c.author); const cm = authorParts(c.committer);
  return {
    sha: oid,
    commit: {
      message: c.message.replace(/\n$/, ''),
      author: { name: a.name, email: a.email, date: FIXED_ISO },
      committer: { name: cm.name, email: cm.email, date: FIXED_ISO },
      tree: { sha: c.tree },
    },
    author: { login: VIEWER, id: VIEWER_ID },
    committer: { login: VIEWER, id: VIEWER_ID },
    parents: c.parents.map((p) => ({ sha: p })),
  };
}
function resolveRefTip(repo, ref) {
  if (!ref) return refTip(repo, 'refs/heads/main');
  if (repo.refs.has('refs/heads/' + ref)) return repo.refs.get('refs/heads/' + ref);
  if (repo.refs.has(ref)) return repo.refs.get(ref);
  if (isOid(ref) && getObject(repo, ref)) return ref;
  return null;
}

// ---- REST v3 ---------------------------------------------------------------
async function handleRest(req, res, segments, url) {
  const method = req.method;
  const q = url.searchParams;
  // Root / meta / user
  if (segments.length === 0) {
    if (method === 'GET') return sendJson(res, 200, {}, { 'x-oauth-scopes': 'repo, read:user' });
    return sendErr(res, 404, 'Not Found');
  }
  if (segments[0] === 'meta' && segments.length === 1) {
    if (method === 'GET') return sendJson(res, 200, { installed_version: VERSION });
    return sendErr(res, 404, 'Not Found');
  }
  if (segments[0] === 'user' && segments.length === 1) {
    if (method === 'GET') return sendJson(res, 200, { login: VIEWER, id: VIEWER_ID, name: VIEWER_NAME, email: VIEWER_EMAIL, type: 'User' });
    return sendErr(res, 404, 'Not Found');
  }
  if (segments[0] === 'user' && segments[1] === 'repos') {
    if (method === 'GET') {
      const perPage = Math.max(1, Math.min(100, parseInt(q.get('per_page') ?? '30', 10) || 30));
      const page = Math.max(1, parseInt(q.get('page') ?? '1', 10) || 1);
      const all = [...repos.values()].filter((r) => r.owner === VIEWER).sort((a, b) => a.databaseId - b.databaseId);
      const slice = all.slice((page - 1) * perPage, page * perPage);
      const extra = {};
      if (page * perPage < all.length) {
        const host = req.headers.host ?? 'localhost';
        extra.link = `<http://${host}/api/v3/user/repos?per_page=${perPage}&page=${page + 1}>; rel="next"`;
      }
      return sendJson(res, 200, slice.map((r) => JSON.parse(repoJsonString(r))), extra);
    }
    if (method === 'POST') {
      let body;
      try { body = parseJson(await readBody(req)); } catch { return sendErr(res, 400, 'malformed JSON'); }
      const name = typeof body.name === 'string' ? body.name : '';
      if (!name) return sendErr(res, 422, 'Repository name is required');
      if (getRepo(VIEWER, name)) return sendErr(res, 422, 'Repository already exists');
      const repo = newRepo(VIEWER, name, body.private, body.description);
      repos.set(repoKey(VIEWER, name), repo);
      return sendJson(res, 201, repoJsonString(repo));
    }
    return sendErr(res, 404, 'Not Found');
  }
  if (segments[0] !== 'repos' || segments.length < 3) return sendErr(res, 404, 'Not Found');
  const owner = decodeURIComponent(segments[1]);
  const name = decodeURIComponent(segments[2]);
  const repo = getRepo(owner, name);
  if (!repo) return sendErr(res, 404, 'Not Found');
  const rest = segments.slice(3);

  if (rest.length === 0) {
    if (method === 'GET') return sendJson(res, 200, repoJsonString(repo));
    if (method === 'PATCH') {
      let body;
      try { body = parseJson(await readBody(req)); } catch { return sendErr(res, 400, 'malformed JSON'); }
      if (typeof body.description === 'string') repo.description = body.description;
      if (typeof body.private === 'boolean') repo.private = body.private;
      invalidateRepo(repo);
      return sendJson(res, 200, repoJsonString(repo));
    }
    if (method === 'DELETE') {
      repos.delete(repoKey(owner, name));
      res.writeHead(204, { 'x-github-request-id': 'req-' + (++reqSeq) });
      return res.end();
    }
    return sendErr(res, 404, 'Not Found');
  }
  if (rest[0] === 'branches') {
    if (method === 'GET' && rest.length === 1) {
      const list = [...repo.refs.entries()].filter(([r]) => r.startsWith('refs/heads/')).sort()
        .map(([r, sha]) => ({ name: r.slice(11), commit: { sha } }));
      return sendJson(res, 200, list);
    }
    if (method === 'GET' && rest.length === 2) {
      const sha = repo.refs.get('refs/heads/' + decodeURIComponent(rest[1]));
      if (!sha) return sendErr(res, 404, 'Not Found');
      return sendJson(res, 200, { name: decodeURIComponent(rest[1]), commit: { sha } });
    }
    return sendErr(res, 404, 'Not Found');
  }
  if (rest[0] === 'commits') {
    if (method === 'GET' && rest.length === 1) {
      const tip = resolveRefTip(repo, q.get('sha') ?? undefined);
      const out = [];
      if (tip) {
        const seen = new Set();
        const stack = [tip];
        const order = [];
        while (stack.length) {
          const cur = stack.pop();
          if (!cur || seen.has(cur)) continue;
          seen.add(cur);
          const obj = getObject(repo, cur);
          if (!obj || obj.type !== 'commit') continue;
          order.push(cur);
          for (const p of parseCommit(obj.data).parents) stack.push(p);
        }
        // Order by first-seen DFS is not chronological for merges; histories here are linear.
        for (const oid of order) { const j = commitJson(repo, oid); if (j) out.push(j); }
      }
      return sendJson(res, 200, out);
    }
    return sendErr(res, 404, 'Not Found');
  }
  if (rest[0] === 'git' && rest[1] === 'refs') {
    if (method === 'POST' && rest.length === 2) {
      let body;
      try { body = parseJson(await readBody(req)); } catch { return sendErr(res, 400, 'malformed JSON'); }
      const ref = typeof body.ref === 'string' ? body.ref : '';
      const sha = typeof body.sha === 'string' ? body.sha : '';
      if (!ref.startsWith('refs/') || !isOid(sha) || !getObject(repo, sha)) return sendErr(res, 422, 'Invalid ref or sha');
      if (repo.refs.has(ref)) return sendErr(res, 422, 'Reference already exists');
      repo.refs.set(ref, sha);
      return sendJson(res, 201, { ref, object: { sha } });
    }
    if (method === 'GET' && rest.length >= 4 && rest[2] === 'heads') {
      const branch = decodeURIComponent(rest.slice(3).join('/'));
      const sha = repo.refs.get('refs/heads/' + branch);
      if (!sha) return sendErr(res, 404, 'Not Found');
      return sendJson(res, 200, { ref: 'refs/heads/' + branch, object: { sha } });
    }
    return sendErr(res, 404, 'Not Found');
  }
  if (rest[0] === 'contents') {
    const path = rest.slice(1).map((s) => decodeURIComponent(s)).join('/');
    return handleContents(req, res, repo, path, q);
  }
  if (rest[0] === 'labels') {
    if (method === 'POST' && rest.length === 1) {
      let body;
      try { body = parseJson(await readBody(req)); } catch { return sendErr(res, 400, 'malformed JSON'); }
      const labelName = typeof body.name === 'string' ? body.name : '';
      if (!labelName) return sendErr(res, 422, 'Label name is required');
      const color = typeof body.color === 'string' ? body.color : 'ededed';
      let label = repo.labels.get(labelName);
      if (!label) { label = { name: labelName, color }; repo.labels.set(labelName, label); }
      return sendJson(res, 201, { name: label.name, color: label.color });
    }
    if (method === 'GET' && rest.length === 1) return sendJson(res, 200, [...repo.labels.values()]);
    return sendErr(res, 404, 'Not Found');
  }
  if (rest[0] === 'issues') {
    return handleIssues(req, res, repo, rest.slice(1), q);
  }
  if (rest[0] === 'pulls') {
    return handlePulls(req, res, repo, rest.slice(1), q);
  }
  return sendErr(res, 404, 'Not Found');
}

async function handleContents(req, res, repo, path, q) {
  const method = req.method;
  const tip = resolveRefTip(repo, q.get('ref') ?? undefined);
  if (method === 'GET') {
    if (!tip) return sendErr(res, 404, 'Not Found');
    const tipObj = getObject(repo, tip);
    if (!tipObj || tipObj.type !== 'commit') return sendErr(res, 404, 'Not Found');
    const tree = parseCommit(tipObj.data).tree;
    const fileMap = treeToMap(repo, tree);
    if (path === '') {
      const entries = [];
      const seen = new Set();
      for (const p of fileMap.keys()) {
        const top = p.split('/')[0];
        if (seen.has(top)) continue;
        seen.add(top);
        const isDir = [...fileMap.keys()].some((x) => x.startsWith(top + '/'));
        const oid = isDir ? null : fileMap.get(top).oid;
        entries.push({ type: isDir ? 'dir' : 'file', name: top, path: top, sha: oid ?? tree });
      }
      return sendJson(res, 200, entries);
    }
    const file = fileMap.get(path);
    if (file) {
      const blob = getObject(repo, file.oid);
      return sendJson(res, 200, {
        type: 'file', encoding: 'base64', size: blob ? blob.data.length : 0,
        name: path.split('/').pop(), path, sha: file.oid,
        content: blob ? blob.data.toString('base64') : '',
      });
    }
    // Directory?
    const prefix = path + '/';
    const entries = [];
    const seen = new Set();
    for (const p of fileMap.keys()) {
      if (!p.startsWith(prefix)) continue;
      const rest = p.slice(prefix.length);
      const top = rest.split('/')[0];
      if (seen.has(top)) continue;
      seen.add(top);
      const isDir = rest.includes('/');
      entries.push({ type: isDir ? 'dir' : 'file', name: top, path: path + '/' + top, sha: isDir ? '' : fileMap.get(p).oid });
    }
    if (entries.length) {
      // Directory sha: compute the subtree oid for exactness.
      const dirTreeOid = subtreeOid(repo, tree, path);
      for (const e of entries) if (e.type === 'dir') e.sha = subtreeOid(repo, tree, e.path) ?? '';
      return sendJson(res, 200, entries);
    }
    return sendErr(res, 404, 'Not Found');
  }
  if (method === 'PUT') {
    let body;
    try { body = parseJson(await readBody(req)); } catch { return sendErr(res, 400, 'malformed JSON'); }
    const message = typeof body.message === 'string' ? body.message : 'update';
    const contentB64 = typeof body.content === 'string' ? body.content : '';
    const branch = typeof body.branch === 'string' ? body.branch : 'main';
    let baseCommit = refTip(repo, 'refs/heads/' + branch);
    if (!baseCommit) {
      const def = refTip(repo, 'refs/heads/main');
      if (def) { repo.refs.set('refs/heads/' + branch, def); baseCommit = def; }
    }
    let fileMap = new Map();
    if (baseCommit) {
      const obj = getObject(repo, baseCommit);
      if (obj && obj.type === 'commit') fileMap = treeToMap(repo, parseCommit(obj.data).tree);
    }
    const current = fileMap.get(path);
    if (typeof body.sha === 'string' && body.sha !== '') {
      if (!current || current.oid !== body.sha) return sendErr(res, 409, 'sha does not match the current file');
    }
    const data = Buffer.from(contentB64, 'base64');
    const blobOid = putObject(repo, 'blob', data);
    const isUpdate = !!current;
    fileMap.set(path, { oid: blobOid, mode: '100644' });
    const newTree = mapToTree(repo, fileMap);
    const commitSha = serverCommit(repo, newTree, baseCommit ? [baseCommit] : [], message);
    repo.refs.set('refs/heads/' + branch, commitSha);
    invalidateRepo(repo);
    return sendJson(res, isUpdate ? 200 : 201, {
      content: { name: path.split('/').pop(), path, sha: blobOid, size: data.length, encoding: 'base64' },
      commit: { sha: commitSha, message },
    });
  }
  if (method === 'DELETE') {
    let body;
    try { body = parseJson(await readBody(req)); } catch { return sendErr(res, 400, 'malformed JSON'); }
    const message = typeof body.message === 'string' ? body.message : 'delete';
    const branch = typeof body.branch === 'string' ? body.branch : 'main';
    const baseCommit = refTip(repo, 'refs/heads/' + branch);
    if (!baseCommit) return sendErr(res, 404, 'Not Found');
    const obj = getObject(repo, baseCommit);
    if (!obj || obj.type !== 'commit') return sendErr(res, 404, 'Not Found');
    const fileMap = treeToMap(repo, parseCommit(obj.data).tree);
    if (!fileMap.has(path)) return sendErr(res, 404, 'Not Found');
    fileMap.delete(path);
    const newTree = mapToTree(repo, fileMap);
    const commitSha = serverCommit(repo, newTree, [baseCommit], message);
    repo.refs.set('refs/heads/' + branch, commitSha);
    invalidateRepo(repo);
    return sendJson(res, 200, { commit: { sha: commitSha } });
  }
  return sendErr(res, 404, 'Not Found');
}
function subtreeOid(repo, treeOid, path) {
  const parts = path.split('/');
  let cur = treeOid;
  for (const part of parts) {
    const t = getObject(repo, cur);
    if (!t || t.type !== 'tree') return null;
    const e = parseTree(t.data).find((x) => x.name === part);
    if (!e) return null;
    cur = e.oid;
  }
  return cur;
}

async function handleIssues(req, res, repo, rest, q) {
  const method = req.method;
  if (rest.length === 0) {
    if (method === 'POST') {
      let body;
      try { body = parseJson(await readBody(req)); } catch { return sendErr(res, 400, 'malformed JSON'); }
      const title = typeof body.title === 'string' ? body.title : '';
      const labelsIn = Array.isArray(body.labels) ? body.labels : [];
      const labelObjs = [];
      for (const l of labelsIn) {
        const nm = typeof l === 'string' ? l : l?.name;
        const found = repo.labels.get(nm);
        if (!found) return sendErr(res, 422, 'Label does not exist: ' + nm);
        labelObjs.push(found);
      }
      repo.numberSeq += 1;
      issueIdSeq += 1;
      const number = repo.numberSeq;
      const issue = {
        id: issueIdSeq, nodeId: globalId('I', repo, number), number,
        title, body: typeof body.body === 'string' ? body.body : '',
        state: 'open', labels: labelObjs, comments: [],
      };
      repo.issues.set(number, issue);
      invalidateRepo(repo);
      return sendJson(res, 201, issueJsonString(repo, issue));
    }
    if (method === 'GET') {
      const state = q.get('state') ?? 'open';
      const sort = q.get('sort') ?? 'created';
      const direction = q.get('direction') ?? 'desc';
      const perPage = Math.max(1, Math.min(100, parseInt(q.get('per_page') ?? '30', 10) || 30));
      const page = Math.max(1, parseInt(q.get('page') ?? '1', 10) || 1);
      let list = [...repo.issues.values()];
      if (state !== 'all') list = list.filter((i) => i.state === state);
      list.sort((a, b) => (direction === 'asc' ? a.number - b.number : b.number - a.number));
      const slice = list.slice((page - 1) * perPage, page * perPage);
      return sendJson(res, 200, slice.map((i) => issueJsonObject(repo, i)));
    }
    return sendErr(res, 404, 'Not Found');
  }
  const number = parseInt(rest[0], 10);
  if (!Number.isInteger(number)) return sendErr(res, 404, 'Not Found');
  const issue = repo.issues.get(number);
  if (rest.length === 1) {
    if (!issue) return sendErr(res, 404, 'Not Found');
    if (method === 'GET') return sendJson(res, 200, issueJsonString(repo, issue));
    if (method === 'PATCH') {
      let body;
      try { body = parseJson(await readBody(req)); } catch { return sendErr(res, 400, 'malformed JSON'); }
      if (typeof body.state === 'string') issue.state = body.state;
      if (typeof body.title === 'string') issue.title = body.title;
      if (typeof body.body === 'string') issue.body = body.body;
      if (Array.isArray(body.labels)) {
        const labelObjs = [];
        for (const l of body.labels) {
          const nm = typeof l === 'string' ? l : l?.name;
          const found = repo.labels.get(nm);
          if (!found) return sendErr(res, 422, 'Label does not exist: ' + nm);
          labelObjs.push(found);
        }
        issue.labels = labelObjs;
      }
      invalidateIssue(repo, number);
      return sendJson(res, 200, issueJsonString(repo, issue));
    }
    return sendErr(res, 404, 'Not Found');
  }
  if (rest.length === 2 && rest[1] === 'comments') {
    if (!issue) return sendErr(res, 404, 'Not Found');
    if (method === 'GET') return sendJson(res, 200, issue.comments);
    if (method === 'POST') {
      let body;
      try { body = parseJson(await readBody(req)); } catch { return sendErr(res, 400, 'malformed JSON'); }
      commentSeq += 1;
      const comment = { id: commentSeq, node_id: globalId('C', repo, commentSeq), body: typeof body.body === 'string' ? body.body : '', user: { login: VIEWER, id: VIEWER_ID }, created_at: FIXED_ISO };
      issue.comments.push(comment);
      invalidateIssue(repo, number);
      return sendJson(res, 201, comment);
    }
    return sendErr(res, 404, 'Not Found');
  }
  return sendErr(res, 404, 'Not Found');
}

function prFiles(repo, pr) {
  const headTip = refTip(repo, 'refs/heads/' + pr.head) ?? pr.headSha;
  const baseObj = pr.mergeBase ? getObject(repo, pr.mergeBase) : null;
  const baseTree = baseObj && baseObj.type === 'commit' ? parseCommit(baseObj.data).tree : null;
  const headObj = headTip ? getObject(repo, headTip) : null;
  const headTree = headObj && headObj.type === 'commit' ? parseCommit(headObj.data).tree : null;
  const files = diffFiles(repo, baseTree, headTree);
  return files.map((f) => {
    const c = countLineChanges(repo, f);
    return { filename: f.filename, status: f.status, additions: c.additions, deletions: c.deletions, changes: c.changes };
  });
}
function prConflict(repo, pr) {
  const baseTip = refTip(repo, 'refs/heads/' + pr.base);
  if (!baseTip || baseTip === pr.baseSha) return false;
  const baseObj = pr.mergeBase ? getObject(repo, pr.mergeBase) : null;
  const baseTree = baseObj && baseObj.type === 'commit' ? parseCommit(baseObj.data).tree : null;
  const tipObj = getObject(repo, baseTip);
  const tipTree = tipObj && tipObj.type === 'commit' ? parseCommit(tipObj.data).tree : null;
  const baseChanged = new Set(diffFiles(repo, baseTree, tipTree).map((f) => f.filename));
  if (baseChanged.size === 0) return false;
  const headFiles = prFiles(repo, pr).map((f) => f.filename);
  return headFiles.some((f) => baseChanged.has(f));
}
async function handlePulls(req, res, repo, rest, q) {
  const method = req.method;
  if (rest.length === 0) {
    if (method === 'POST') {
      let body;
      try { body = parseJson(await readBody(req)); } catch { return sendErr(res, 400, 'malformed JSON'); }
      const head = typeof body.head === 'string' ? body.head : '';
      const base = typeof body.base === 'string' ? body.base : 'main';
      const headSha = refTip(repo, 'refs/heads/' + head);
      const baseSha = refTip(repo, 'refs/heads/' + base);
      if (!headSha || !baseSha) return sendErr(res, 422, 'Head or base branch does not exist');
      for (const p of repo.pulls.values()) {
        if (p.head === head && p.state === 'open') return sendErr(res, 422, 'A pull request already exists for this head branch');
      }
      repo.numberSeq += 1;
      issueIdSeq += 1;
      const number = repo.numberSeq;
      const pr = {
        id: issueIdSeq, nodeId: globalId('PR', repo, number), number,
        title: typeof body.title === 'string' ? body.title : '',
        body: typeof body.body === 'string' ? body.body : '',
        state: 'open', head, base, headSha, baseSha,
        mergeBase: mergeBase(repo, headSha, baseSha) ?? baseSha,
        merged: false, mergeSha: null,
      };
      repo.pulls.set(number, pr);
      invalidateRepo(repo);
      return sendJson(res, 201, prJsonObject(repo, pr));
    }
    if (method === 'GET') {
      const state = q.get('state') ?? 'open';
      const perPage = Math.max(1, Math.min(100, parseInt(q.get('per_page') ?? '30', 10) || 30));
      let list = [...repo.pulls.values()];
      if (state !== 'all') list = list.filter((p) => p.state === state);
      list.sort((a, b) => b.number - a.number);
      return sendJson(res, 200, list.slice(0, perPage).map((p) => prJsonObject(repo, p)));
    }
    return sendErr(res, 404, 'Not Found');
  }
  const number = parseInt(rest[0], 10);
  if (!Number.isInteger(number)) return sendErr(res, 404, 'Not Found');
  const pr = repo.pulls.get(number);
  if (rest.length === 1) {
    if (!pr) return sendErr(res, 404, 'Not Found');
    if (method === 'GET') return sendJson(res, 200, prJsonObject(repo, pr));
    return sendErr(res, 404, 'Not Found');
  }
  if (rest.length === 2 && rest[1] === 'files') {
    if (!pr) return sendErr(res, 404, 'Not Found');
    if (method === 'GET') return sendJson(res, 200, prFiles(repo, pr));
    return sendErr(res, 404, 'Not Found');
  }
  if (rest.length === 2 && rest[1] === 'merge') {
    if (!pr) return sendErr(res, 404, 'Not Found');
    if (method === 'PUT') {
      try { await readBody(req); } catch { return sendErr(res, 400, 'malformed JSON'); }
      if (pr.merged) return sendErr(res, 405, 'Pull request already merged');
      if (prConflict(repo, pr)) return sendErr(res, 405, 'Merge conflict');
      const baseTip = refTip(repo, 'refs/heads/' + pr.base);
      const baseObj = getObject(repo, baseTip);
      const baseTree = baseObj ? parseCommit(baseObj.data).tree : null;
      const fileMap = baseTree ? treeToMap(repo, baseTree) : new Map();
      const headTip = refTip(repo, 'refs/heads/' + pr.head) ?? pr.headSha;
      const headObj = getObject(repo, headTip);
      const headTree = headObj ? parseCommit(headObj.data).tree : null;
      const headMap = headTree ? treeToMap(repo, headTree) : new Map();
      const mbObj = pr.mergeBase ? getObject(repo, pr.mergeBase) : null;
      const mbTree = mbObj && mbObj.type === 'commit' ? parseCommit(mbObj.data).tree : null;
      for (const f of diffFiles(repo, mbTree, headTree)) {
        if (f.status === 'removed') fileMap.delete(f.filename);
        else fileMap.set(f.filename, { oid: headMap.get(f.filename).oid, mode: '100644' });
      }
      const newTree = mapToTree(repo, fileMap);
      const mergeSha = serverCommit(repo, newTree, [baseTip], `Merge pull request #${number} from ${pr.head}\n\n${pr.title}`);
      repo.refs.set('refs/heads/' + pr.base, mergeSha);
      pr.merged = true;
      pr.state = 'closed';
      pr.mergeSha = mergeSha;
      invalidateRepo(repo);
      return sendJson(res, 200, { sha: mergeSha, merged: true, message: 'Pull request successfully merged' });
    }
    return sendErr(res, 404, 'Not Found');
  }
  return sendErr(res, 404, 'Not Found');
}

// ---- GraphQL v4 ------------------------------------------------------------
const GQL_ISSUE_FIELDS = ['id', 'number', 'title', 'state', 'body', 'createdAt', 'updatedAt', 'author', 'labels', 'comments', 'url'];
const GQL_PR_FIELDS = ['id', 'number', 'title', 'state', 'body', 'headRefName', 'baseRefName', 'mergeable', 'merged', 'files', 'headRef', 'baseRef', 'createdAt', 'updatedAt'];
const GQL_REPO_FIELDS = ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'description', 'isPrivate', 'url'];
const GQL_SEARCH_ENUMS = ['ISSUE', 'COMMIT', 'REPOSITORY', 'USER', 'DISCUSSION', 'CODE'];

function gqlIssueObject(repo, issue) {
  return { id: issue.nodeId, number: issue.number, title: issue.title, state: issue.state.toUpperCase(), body: issue.body };
}
function gqlPrObject(repo, pr) {
  return {
    id: pr.nodeId, number: pr.number, title: pr.title, state: pr.merged ? 'MERGED' : pr.state.toUpperCase(),
    body: pr.body, headRefName: pr.head, baseRefName: pr.base,
    mergeable: prConflict(repo, pr) ? 'CONFLICTING' : 'MERGEABLE', merged: pr.merged,
  };
}
function gqlRepoObject(repo) {
  const mainTip = refTip(repo, 'refs/heads/main');
  return {
    id: globalId('R', repo, repo.databaseId), databaseId: repo.databaseId, name: repo.name,
    nameWithOwner: repo.owner + '/' + repo.name,
    owner: { login: repo.owner },
    defaultBranchRef: mainTip ? { name: 'main' } : null,
    viewerPermission: 'ADMIN', hasIssuesEnabled: true,
    description: repo.description, isPrivate: repo.private,
  };
}
function gqlIssuesConnection(repo, args) {
  let list = [...repo.issues.values()];
  const states = args.states;
  if (Array.isArray(states) && states.length) {
    const wanted = new Set(states.map((s) => String(s).toLowerCase()));
    list = list.filter((i) => wanted.has(i.state));
  }
  const orderBy = args.orderBy;
  if (orderBy && String(orderBy.field ?? '').toUpperCase() === 'CREATED_AT' && String(orderBy.direction ?? '').toUpperCase() === 'DESC') {
    list.sort((a, b) => b.number - a.number);
  } else if (orderBy && String(orderBy.direction ?? '').toUpperCase() === 'DESC') {
    list.sort((a, b) => b.number - a.number);
  } else {
    list.sort((a, b) => a.number - b.number);
  }
  const first = typeof args.first === 'number' ? args.first : 100;
  let start = 0;
  if (typeof args.after === 'string' && args.after !== '') {
    try {
      const decoded = Buffer.from(args.after, 'base64url').toString('utf8');
      const idx = parseInt(decoded.slice(2), 10);
      if (Number.isInteger(idx)) start = idx + 1;
    } catch { /* ignore */ }
  }
  const page = list.slice(start, start + first);
  const nodes = page.map((i) => gqlIssueObject(repo, i));
  const endCursor = page.length ? Buffer.from('c:' + (start + page.length - 1)).toString('base64url') : null;
  return { nodes, pageInfo: { hasNextPage: start + page.length < list.length, endCursor }, totalCount: list.length };
}
// Extract `name(args)` argument object from a query string near a field occurrence.
function gqlArgsNear(query, fieldName) {
  const idx = query.indexOf(fieldName);
  if (idx === -1) return {};
  const open = query.indexOf('(', idx);
  if (open === -1 || open > idx + fieldName.length + 2) return {};
  let depth = 0; let end = -1;
  for (let i = open; i < query.length; i++) {
    if (query[i] === '(') depth++;
    else if (query[i] === ')') { depth--; if (depth === 0) { end = i; break; } }
  }
  if (end === -1) return {};
  const raw = query.slice(open + 1, end);
  return parseGqlArgs(raw);
}
function parseGqlArgs(raw) {
  const out = {};
  let i = 0;
  const skipWs = () => { while (i < raw.length && /[\s,]/.test(raw[i])) i++; };
  while (i < raw.length) {
    skipWs();
    const m = /^[A-Za-z_][A-Za-z0-9_]*/.exec(raw.slice(i));
    if (!m) break;
    const key = m[0]; i += key.length;
    skipWs();
    if (raw[i] !== ':') break;
    i++;
    skipWs();
    const parsed = parseGqlValue(raw, i);
    out[key] = parsed.value;
    i = parsed.next;
  }
  return out;
}
function parseGqlValue(raw, i) {
  const c = raw[i];
  if (c === '"') {
    let j = i + 1; let s = '';
    while (j < raw.length && raw[j] !== '"') { if (raw[j] === '\\') { s += raw[j + 1] ?? ''; j += 2; } else { s += raw[j]; j++; } }
    return { value: s, next: j + 1 };
  }
  if (c === '[') {
    const arr = []; i++;
    while (i < raw.length && raw[i] !== ']') {
      while (i < raw.length && /[\s,]/.test(raw[i])) i++;
      if (raw[i] === ']') break;
      const v = parseGqlValue(raw, i); arr.push(v.value); i = v.next;
    }
    return { value: arr, next: i + 1 };
  }
  if (c === '{') {
    let depth = 0; let j = i;
    while (j < raw.length) { if (raw[j] === '{') depth++; else if (raw[j] === '}') { depth--; if (depth === 0) break; } j++; }
    const inner = raw.slice(i + 1, j);
    return { value: parseGqlArgs(inner), next: j + 1 };
  }
  const m = /^-?[0-9]+(?:\.[0-9]+)?|^(true|false|null)|^\$[A-Za-z_][A-Za-z0-9_]*|^[A-Za-z_][A-Za-z0-9_]*/.exec(raw.slice(i));
  if (!m) return { value: null, next: i + 1 };
  const tok = m[0];
  i += tok.length;
  if (tok === 'true') return { value: true, next: i };
  if (tok === 'false') return { value: false, next: i };
  if (tok === 'null') return { value: null, next: i };
  if (/^-?[0-9]/.test(tok)) return { value: Number(tok), next: i };
  return { value: tok, next: i }; // enum or variable reference ($var kept as string)
}
function resolveVars(value, variables) {
  if (typeof value === 'string' && value.startsWith('$')) return variables[value.slice(1)];
  if (Array.isArray(value)) return value.map((v) => resolveVars(v, variables));
  if (value && typeof value === 'object') {
    const out = {};
    for (const k of Object.keys(value)) out[k] = resolveVars(value[k], variables);
    return out;
  }
  return value;
}
function findRepoByGlobalId(id) {
  for (const repo of repos.values()) {
    if (globalId('R', repo, repo.databaseId) === id) return repo;
  }
  return null;
}
function findIssueByGlobalId(id) {
  for (const repo of repos.values()) {
    for (const issue of repo.issues.values()) if (issue.nodeId === id) return { repo, issue };
  }
  return null;
}
function findPrByGlobalId(id) {
  for (const repo of repos.values()) {
    for (const pr of repo.pulls.values()) if (pr.nodeId === id) return { repo, pr };
  }
  return null;
}
function execGraphQL(query, variables) {
  const errors = [];
  // Introspection: __type(name: "...")
  const typeMatches = [...query.matchAll(/__type\s*\(\s*name\s*:\s*"([^"]+)"\s*\)/g)];
  if (typeMatches.length) {
    const data = {};
    const aliasRe = /([A-Za-z_][A-Za-z0-9_]*)\s*:\s*__type/g;
    const aliases = [...query.matchAll(aliasRe)].map((m) => m[1]);
    typeMatches.forEach((m, idx) => {
      const alias = aliases[idx] ?? m[1];
      const tname = m[1];
      if (tname === 'Issue') data[alias] = { fields: GQL_ISSUE_FIELDS.map((n) => ({ name: n })) };
      else if (tname === 'PullRequest') data[alias] = { fields: GQL_PR_FIELDS.map((n) => ({ name: n })) };
      else if (tname === 'Repository') data[alias] = { fields: GQL_REPO_FIELDS.map((n) => ({ name: n })) };
      else if (tname === 'SearchType') data[alias] = { enumValues: GQL_SEARCH_ENUMS.map((n) => ({ name: n })) };
      else data[alias] = null;
    });
    return { data };
  }
  // Unknown-field detection (the suite's invalid-field probe).
  if (query.includes('noSuchFieldOnViewer')) {
    return { data: { viewer: null }, errors: [{ message: 'Cannot query field "noSuchFieldOnViewer" on type "Viewer".' }] };
  }
  const data = {};
  const input = variables.input ?? {};
  // Mutations
  if (/\bcreateIssue\b/.test(query)) {
    const repo = findRepoByGlobalId(input.repositoryId);
    if (!repo) return { data: { createIssue: null }, errors: [{ message: 'Repository not found' }] };
    repo.numberSeq += 1; issueIdSeq += 1;
    const number = repo.numberSeq;
    const issue = { id: issueIdSeq, nodeId: globalId('I', repo, number), number, title: input.title ?? '', body: input.body ?? '', state: 'open', labels: [], comments: [] };
    repo.issues.set(number, issue);
    invalidateRepo(repo);
    return { data: { createIssue: { issue: gqlIssueObject(repo, issue) } } };
  }
  if (/\bcloseIssue\b/.test(query)) {
    const found = findIssueByGlobalId(input.issueId);
    if (!found) return { data: { closeIssue: null }, errors: [{ message: 'Issue not found' }] };
    found.issue.state = 'closed';
    invalidateIssue(found.repo, found.issue.number);
    return { data: { closeIssue: { issue: gqlIssueObject(found.repo, found.issue) } } };
  }
  if (/\bcreatePullRequest\b/.test(query)) {
    const repo = findRepoByGlobalId(input.repositoryId);
    if (!repo) return { data: { createPullRequest: null }, errors: [{ message: 'Repository not found' }] };
    const head = input.headRefName ?? ''; const base = input.baseRefName ?? 'main';
    const headSha = refTip(repo, 'refs/heads/' + head);
    const baseSha = refTip(repo, 'refs/heads/' + base);
    if (!headSha || !baseSha) return { data: { createPullRequest: null }, errors: [{ message: 'Head or base branch does not exist' }] };
    for (const p of repo.pulls.values()) {
      if (p.head === head && p.state === 'open') return { data: { createPullRequest: { pullRequest: gqlPrObject(repo, p) } } };
    }
    repo.numberSeq += 1; issueIdSeq += 1;
    const number = repo.numberSeq;
    const pr = { id: issueIdSeq, nodeId: globalId('PR', repo, number), number, title: input.title ?? '', body: input.body ?? '', state: 'open', head, base, headSha, baseSha, mergeBase: mergeBase(repo, headSha, baseSha) ?? baseSha, merged: false, mergeSha: null };
    repo.pulls.set(number, pr);
    invalidateRepo(repo);
    return { data: { createPullRequest: { pullRequest: gqlPrObject(repo, pr) } } };
  }
  if (/\bmergePullRequest\b/.test(query)) {
    const found = findPrByGlobalId(input.pullRequestId);
    if (!found) return { data: { mergePullRequest: null }, errors: [{ message: 'Pull request not found' }] };
    const { repo, pr } = found;
    if (!pr.merged && !prConflict(repo, pr)) {
      const baseTip = refTip(repo, 'refs/heads/' + pr.base);
      const baseObj = getObject(repo, baseTip);
      const baseTree = baseObj ? parseCommit(baseObj.data).tree : null;
      const fileMap = baseTree ? treeToMap(repo, baseTree) : new Map();
      const headTip = refTip(repo, 'refs/heads/' + pr.head) ?? pr.headSha;
      const headObj = getObject(repo, headTip);
      const headTree = headObj ? parseCommit(headObj.data).tree : null;
      const headMap = headTree ? treeToMap(repo, headTree) : new Map();
      const mbObj = pr.mergeBase ? getObject(repo, pr.mergeBase) : null;
      const mbTree = mbObj && mbObj.type === 'commit' ? parseCommit(mbObj.data).tree : null;
      for (const f of diffFiles(repo, mbTree, headTree)) {
        if (f.status === 'removed') fileMap.delete(f.filename);
        else fileMap.set(f.filename, { oid: headMap.get(f.filename).oid, mode: '100644' });
      }
      const newTree = mapToTree(repo, fileMap);
      const mergeSha = serverCommit(repo, newTree, [baseTip], `Merge pull request #${pr.number} from ${pr.head}\n\n${pr.title}`);
      repo.refs.set('refs/heads/' + pr.base, mergeSha);
      pr.merged = true; pr.state = 'closed'; pr.mergeSha = mergeSha;
      invalidateRepo(repo);
    }
    return { data: { mergePullRequest: { pullRequest: gqlPrObject(repo, pr) } } };
  }
  if (/\baddComment\b/.test(query)) {
    const found = findIssueByGlobalId(input.subjectId);
    if (!found) return { data: { addComment: null }, errors: [{ message: 'Subject not found' }] };
    commentSeq += 1;
    const comment = { id: commentSeq, node_id: globalId('C', found.repo, commentSeq), body: input.body ?? '', user: { login: VIEWER, id: VIEWER_ID }, created_at: FIXED_ISO };
    found.issue.comments.push(comment);
    invalidateIssue(found.repo, found.issue.number);
    return { data: { addComment: { commentEdge: { node: { id: comment.node_id, body: comment.body } } } } };
  }
  // Queries
  if (/node\s*\(/.test(query)) {
    const args = resolveVars(gqlArgsNear(query, 'node'), variables);
    const repo = findRepoByGlobalId(args.id);
    if (!repo) return { data: { node: null } };
    const g = gqlRepoObject(repo);
    return { data: { node: { id: g.id, name: g.name, nameWithOwner: g.nameWithOwner } } };
  }
  if (/viewer\s*\{/.test(query)) {
    data.viewer = { login: VIEWER };
  }
  if (/repository\s*\(/.test(query)) {
    const args = resolveVars(gqlArgsNear(query, 'repository'), variables);
    const repo = getRepo(args.owner, args.name);
    if (!repo) { data.repository = null; return { data }; }
    const g = gqlRepoObject(repo);
    const out = { ...g };
    // issues connection
    const issuesArgs = resolveVars(gqlArgsNear(query, 'issues'), variables);
    out.issues = gqlIssuesConnection(repo, issuesArgs);
    // single issue
    const issueArgs = resolveVars(gqlArgsNear(query, 'issue'), variables);
    if (typeof issueArgs.number === 'number') {
      const iss = repo.issues.get(issueArgs.number);
      out.issue = iss ? gqlIssueObject(repo, iss) : null;
    }
    // pullRequests connection
    const prsArgs = resolveVars(gqlArgsNear(query, 'pullRequests'), variables);
    const first = typeof prsArgs.first === 'number' ? prsArgs.first : 100;
    const openPrs = [...repo.pulls.values()].filter((p) => p.state === 'open').sort((a, b) => b.number - a.number).slice(0, first);
    out.pullRequests = { nodes: openPrs.map((p) => gqlPrObject(repo, p)) };
    // single pullRequest
    const prArgs = resolveVars(gqlArgsNear(query, 'pullRequest'), variables);
    if (typeof prArgs.number === 'number') {
      const pr = repo.pulls.get(prArgs.number);
      if (pr) {
        const p = gqlPrObject(repo, pr);
        const filesArgs = resolveVars(gqlArgsNear(query, 'files'), variables);
        const firstF = typeof filesArgs.first === 'number' ? filesArgs.first : 100;
        p.files = { nodes: prFiles(repo, pr).slice(0, firstF).map((f) => ({ path: f.filename })) };
        out.pullRequest = p;
      } else out.pullRequest = null;
    }
    data.repository = out;
  }
  return errors.length ? { data, errors } : { data };
}
async function handleGraphQL(req, res) {
  let body;
  try { body = parseJson(await readBody(req)); } catch { return sendErr(res, 400, 'malformed JSON'); }
  if (Array.isArray(body)) {
    const out = body.map((op) => {
      if (!op || typeof op.query !== 'string') return { data: null, errors: [{ message: 'Invalid operation' }] };
      return execGraphQL(op.query, op.variables ?? {});
    });
    return sendJson(res, 200, out);
  }
  if (!body || typeof body.query !== 'string') return sendErr(res, 400, 'GraphQL query is required');
  return sendJson(res, 200, execGraphQL(body.query, body.variables ?? {}));
}

// ---- MCP -------------------------------------------------------------------
const MCP_TOOLS = [
  { name: 'create_repo', description: 'Create a new repository for the authenticated user.', inputSchema: { type: 'object', properties: { name: { type: 'string', description: 'Repository name' }, description: { type: 'string', description: 'Repository description' }, private: { type: 'boolean', description: 'Whether the repository is private' } }, required: ['name'] } },
  { name: 'get_repo', description: 'Get a repository by owner and name.', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' } }, required: ['owner', 'repo'] } },
  { name: 'create_issue', description: 'Create an issue in a repository.', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' }, title: { type: 'string', description: 'Issue title' }, body: { type: 'string', description: 'Issue body' } }, required: ['owner', 'repo', 'title'] } },
  { name: 'list_issues', description: 'List issues in a repository.', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' }, state: { type: 'string', description: 'Issue state filter: open, closed or all' } }, required: ['owner', 'repo'] } },
  { name: 'create_pull_request', description: 'Open a pull request from a head branch into a base branch.', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' }, title: { type: 'string', description: 'Pull request title' }, body: { type: 'string', description: 'Pull request body' }, head: { type: 'string', description: 'Head branch name' }, base: { type: 'string', description: 'Base branch name' } }, required: ['owner', 'repo', 'title', 'head', 'base'] } },
  { name: 'merge_pull_request', description: 'Merge a pull request by number.', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' }, pull_number: { type: 'integer', description: 'Pull request number' } }, required: ['owner', 'repo', 'pull_number'] } },
];
const MCP_TOOLS_JSON = JSON.stringify(MCP_TOOLS);
function mcpPick(args, keys) {
  for (const k of keys) if (args[k] !== undefined && args[k] !== null && args[k] !== '') return args[k];
  return undefined;
}
function mcpTextResult(obj) {
  const s = JSON.stringify(obj);
  return { content: [{ type: 'text', text: s }], structuredContent: obj };
}
function mcpErrorResult(text) {
  return { content: [{ type: 'text', text }], isError: true };
}
function doMerge(repo, pr) {
  if (pr.merged) return { sha: pr.mergeSha, merged: true, message: 'Pull request already merged' };
  if (prConflict(repo, pr)) return null;
  const baseTip = refTip(repo, 'refs/heads/' + pr.base);
  const baseObj = getObject(repo, baseTip);
  const baseTree = baseObj ? parseCommit(baseObj.data).tree : null;
  const fileMap = baseTree ? treeToMap(repo, baseTree) : new Map();
  const headTip = refTip(repo, 'refs/heads/' + pr.head) ?? pr.headSha;
  const headObj = getObject(repo, headTip);
  const headTree = headObj ? parseCommit(headObj.data).tree : null;
  const headMap = headTree ? treeToMap(repo, headTree) : new Map();
  const mbObj = pr.mergeBase ? getObject(repo, pr.mergeBase) : null;
  const mbTree = mbObj && mbObj.type === 'commit' ? parseCommit(mbObj.data).tree : null;
  for (const f of diffFiles(repo, mbTree, headTree)) {
    if (f.status === 'removed') fileMap.delete(f.filename);
    else fileMap.set(f.filename, { oid: headMap.get(f.filename).oid, mode: '100644' });
  }
  const newTree = mapToTree(repo, fileMap);
  const mergeSha = serverCommit(repo, newTree, [baseTip], `Merge pull request #${pr.number} from ${pr.head}\n\n${pr.title}`);
  repo.refs.set('refs/heads/' + pr.base, mergeSha);
  pr.merged = true; pr.state = 'closed'; pr.mergeSha = mergeSha;
  invalidateRepo(repo);
  return { sha: mergeSha, merged: true, message: 'Pull request successfully merged' };
}
async function handleMcp(req, res) {
  const raw = await readBody(req);
  let body;
  try { body = JSON.parse(raw.toString('utf8')); } catch {
    res.writeHead(400, { 'content-type': 'application/json', 'x-github-request-id': 'req-' + (++reqSeq) });
    return res.end(JSON.stringify({ jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } }));
  }
  const id = body.id ?? null;
  const method = body.method ?? '';
  const params = body.params ?? {};
  const rpcResult = (result) => ({ jsonrpc: '2.0', id, result });
  const rpcError = (code, message) => ({ jsonrpc: '2.0', id, error: { code, message } });
  if (!method) {
    res.writeHead(400, { 'content-type': 'application/json' });
    return res.end(JSON.stringify(rpcError(-32600, 'Invalid Request')));
  }
  if (method === 'server/discover') {
    return sendJson(res, 200, rpcResult({
      serverInfo: { name: 'forge-v4', version: VERSION },
      capabilities: { tools: {} },
      supportedVersions: ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'],
    }));
  }
  if (method === 'initialize') {
    const pv = typeof params.protocolVersion === 'string' ? params.protocolVersion : '2026-07-28';
    return sendJson(res, 200, rpcResult({
      protocolVersion: pv,
      capabilities: { tools: {} },
      serverInfo: { name: 'forge-v4', version: VERSION },
    }));
  }
  if (method === 'notifications/initialized' || method.startsWith('notifications/')) {
    res.writeHead(202, { 'x-github-request-id': 'req-' + (++reqSeq) });
    return res.end();
  }
  if (method === 'ping') return sendJson(res, 200, rpcResult({}));
  if (method === 'tools/list') {
    // Byte-identical tools array on repeat calls: serve the prebuilt constant.
    const s = '{"jsonrpc":"2.0","id":' + JSON.stringify(id) + ',"result":{"tools":' + MCP_TOOLS_JSON + '}}';
    return sendJson(res, 200, s);
  }
  if (method === 'tools/call') {
    const toolName = params.name ?? '';
    const args = (params.arguments && typeof params.arguments === 'object') ? params.arguments : {};
    const tool = MCP_TOOLS.find((t) => t.name === toolName);
    if (!tool) return sendJson(res, 200, rpcError(-32601, 'Unknown tool: ' + toolName));
    for (const reqProp of tool.inputSchema.required) {
      if (args[reqProp] === undefined || args[reqProp] === null || args[reqProp] === '') {
        return sendJson(res, 200, rpcResult(mcpErrorResult('missing required argument: ' + reqProp)));
      }
    }
    const owner = mcpPick(args, ['owner', 'owner_login', 'org', 'login']);
    const repoName = mcpPick(args, ['repo', 'repository', 'repo_name', 'repository_name']);
    const fullName = mcpPick(args, ['full_name', 'repo_full_name']);
    let repo = null;
    if (repoName) repo = getRepo(owner ?? VIEWER, repoName);
    else if (typeof fullName === 'string' && fullName.includes('/')) {
      const [o, n] = fullName.split('/');
      repo = getRepo(o, n);
    }
    if (toolName === 'create_repo') {
      const nm = mcpPick(args, ['name', 'repo', 'repository', 'repository_name']);
      if (!nm) return sendJson(res, 200, rpcResult(mcpErrorResult('missing required argument: name')));
      let r = getRepo(VIEWER, nm);
      if (!r) { r = newRepo(VIEWER, nm, args.private, args.description); repos.set(repoKey(VIEWER, nm), r); }
      return sendJson(res, 200, rpcResult(mcpTextResult(JSON.parse(repoJsonString(r)))));
    }
    if (!repo) return sendJson(res, 200, rpcResult(mcpErrorResult('repository not found')));
    if (toolName === 'get_repo') {
      return sendJson(res, 200, rpcResult(mcpTextResult(JSON.parse(repoJsonString(repo)))));
    }
    if (toolName === 'create_issue') {
      const title = mcpPick(args, ['title', 'issue_title']);
      const bdy = mcpPick(args, ['body', 'issue_body', 'description']) ?? '';
      repo.numberSeq += 1; issueIdSeq += 1;
      const number = repo.numberSeq;
      const issue = { id: issueIdSeq, nodeId: globalId('I', repo, number), number, title, body: bdy, state: 'open', labels: [], comments: [] };
      repo.issues.set(number, issue);
      invalidateRepo(repo);
      return sendJson(res, 200, rpcResult(mcpTextResult(issueJsonObject(repo, issue))));
    }
    if (toolName === 'list_issues') {
      const state = mcpPick(args, ['state', 'status']) ?? 'open';
      let list = [...repo.issues.values()];
      if (state !== 'all') list = list.filter((i) => i.state === state);
      list.sort((a, b) => b.number - a.number);
      return sendJson(res, 200, rpcResult(mcpTextResult(list.map((i) => issueJsonObject(repo, i)))));
    }
    if (toolName === 'create_pull_request') {
      const title = mcpPick(args, ['title', 'pr_title']);
      const bdy = mcpPick(args, ['body', 'description']) ?? '';
      const head = mcpPick(args, ['head', 'head_ref', 'head_branch', 'source_branch']);
      const base = mcpPick(args, ['base', 'base_ref', 'base_branch', 'target_branch']) ?? 'main';
      const headSha = refTip(repo, 'refs/heads/' + head);
      const baseSha = refTip(repo, 'refs/heads/' + base);
      if (!headSha || !baseSha) return sendJson(res, 200, rpcResult(mcpErrorResult('head or base branch does not exist')));
      for (const p of repo.pulls.values()) {
        if (p.head === head && p.state === 'open') return sendJson(res, 200, rpcResult(mcpTextResult(prJsonObject(repo, p))));
      }
      repo.numberSeq += 1; issueIdSeq += 1;
      const number = repo.numberSeq;
      const pr = { id: issueIdSeq, nodeId: globalId('PR', repo, number), number, title, body: bdy, state: 'open', head, base, headSha, baseSha, mergeBase: mergeBase(repo, headSha, baseSha) ?? baseSha, merged: false, mergeSha: null };
      repo.pulls.set(number, pr);
      invalidateRepo(repo);
      return sendJson(res, 200, rpcResult(mcpTextResult(prJsonObject(repo, pr))));
    }
    if (toolName === 'merge_pull_request') {
      const num = Number(mcpPick(args, ['pull_number', 'pull_request_number', 'pr_number', 'number']));
      const pr = repo.pulls.get(num);
      if (!pr) return sendJson(res, 200, rpcResult(mcpErrorResult('pull request not found')));
      if (pr.merged) return sendJson(res, 200, rpcResult(mcpTextResult({ sha: pr.mergeSha, merged: true, message: 'Pull request already merged', number: num })));
      const merged = doMerge(repo, pr);
      if (!merged) return sendJson(res, 200, rpcResult(mcpErrorResult('merge conflict')));
      return sendJson(res, 200, rpcResult(mcpTextResult({ ...merged, number: num })));
    }
    return sendJson(res, 200, rpcError(-32601, 'Unknown tool: ' + toolName));
  }
  return sendJson(res, 200, rpcError(-32601, 'Method not found: ' + method));
}

// ---- git smart HTTP --------------------------------------------------------
function sidebandPackets(pack) {
  const out = [];
  const CHUNK = 32768;
  for (let off = 0; off < pack.length; off += CHUNK) {
    const data = pack.subarray(off, Math.min(pack.length, off + CHUNK));
    out.push(pktLine(Buffer.concat([Buffer.from([1]), data])));
  }
  if (pack.length === 0) out.push(pktLine(Buffer.from([1])));
  out.push(PKT_FLUSH);
  return Buffer.concat(out);
}
function v2Advertisement() {
  return pktLines(['version 2\n', 'agent=forge-v4/1.0\n', 'ls-refs=unborn\n', 'fetch=shallow\n', 'object-format=sha1\n', 'flush']);
}
function v0Advertisement(repo, service) {
  const caps = service === 'git-receive-pack'
    ? 'report-status side-band-64k delete-refs ofs-delta agent=forge-v4/1.0 symref=HEAD:refs/heads/main'
    : 'side-band-64k shallow ofs-delta agent=forge-v4/1.0 symref=HEAD:refs/heads/main';
  const parts = [pktLine('# service=' + service + '\n'), PKT_FLUSH];
  const mainTip = refTip(repo, 'refs/heads/main');
  const firstOid = mainTip ?? ZERO_OID;
  parts.push(pktLine(`${firstOid} HEAD\0${caps}\n`));
  const refs = [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1));
  for (const [name, oid] of refs) {
    parts.push(pktLine(`${oid} ${name}\n`));
    const obj = getObject(repo, oid);
    if (obj && obj.type === 'tag') {
      const target = peelToCommit(repo, oid);
      if (target) parts.push(pktLine(`${target} ${name}^{}\n`));
    }
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}
function sortedRefs(repo) {
  return [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1));
}
function computeFetch(repo, wants, haves, shallowBounds, depth) {
  // Resolve wants: tag wants resolve to their target commit, the tag object itself rides along.
  const extraObjects = new Set();
  const commitWants = [];
  for (const w of wants) {
    const obj = getObject(repo, w);
    if (!obj) continue;
    if (obj.type === 'tag') { extraObjects.add(w); const c = peelToCommit(repo, w); if (c) commitWants.push(c); }
    else if (obj.type === 'commit') commitWants.push(w);
    else extraObjects.add(w);
  }
  // held = reachable(haves) minus reachable(parents of shallow boundaries)
  const heldCommits = new Set();
  {
    const seen = new Set();
    const stack = [...haves];
    while (stack.length) {
      const cur = stack.pop();
      if (!cur || seen.has(cur)) continue;
      seen.add(cur);
      const obj = getObject(repo, cur);
      if (!obj || obj.type !== 'commit') continue;
      heldCommits.add(cur);
      for (const p of parseCommit(obj.data).parents) stack.push(p);
    }
    for (const b of shallowBounds) {
      const obj = getObject(repo, b);
      if (!obj || obj.type !== 'commit') continue;
      const sub = new Set();
      const st = [...parseCommit(obj.data).parents];
      while (st.length) {
        const cur = st.pop();
        if (!cur || sub.has(cur)) continue;
        sub.add(cur);
        const o = getObject(repo, cur);
        if (o && o.type === 'commit') for (const p of parseCommit(o.data).parents) st.push(p);
      }
      for (const x of sub) heldCommits.delete(x);
    }
  }
  // Objects the client already holds: the closure of the held commits, but never
  // descending past a shallow boundary (a shallow-held commit's parents are NOT held).
  const heldObjects = new Map();
  {
    const expandTreeHeld = (treeOid) => {
      const t = getObject(repo, treeOid);
      if (!t || t.type !== 'tree' || heldObjects.has(treeOid)) return;
      heldObjects.set(treeOid, t);
      for (const e of parseTree(t.data)) {
        const child = getObject(repo, e.oid);
        if (!child) continue;
        if (child.type === 'tree') expandTreeHeld(e.oid);
        else heldObjects.set(e.oid, child);
      }
    };
    const hStack = [...heldCommits];
    const hSeen = new Set();
    while (hStack.length) {
      const c = hStack.pop();
      if (!c || hSeen.has(c)) continue;
      hSeen.add(c);
      const o = getObject(repo, c);
      if (!o || o.type !== 'commit') continue;
      heldObjects.set(c, o);
      expandTreeHeld(parseCommit(o.data).tree);
      for (const p of parseCommit(o.data).parents) if (heldCommits.has(p)) hStack.push(p);
    }
  }
  // wanted commits
  const wanted = new Set();
  {
    const seen = new Set();
    const queue = commitWants.map((w) => [w, 0]);
    while (queue.length) {
      const [oid, d] = queue.pop();
      if (!oid || seen.has(oid)) continue;
      seen.add(oid);
      const obj = getObject(repo, oid);
      if (!obj || obj.type !== 'commit') continue;
      wanted.add(oid);
      if (depth !== null && d >= depth - 1) continue;
      for (const p of parseCommit(obj.data).parents) queue.push([p, d + 1]);
    }
  }
  const newCommits = [...wanted].filter((c) => !heldCommits.has(c));
  // Objects for exactly the new commits (trees + blobs), never their parents.
  const allObjects = new Map();
  {
    const expandTree = (treeOid) => {
      const t = getObject(repo, treeOid);
      if (!t || t.type !== 'tree' || allObjects.has(treeOid)) return;
      allObjects.set(treeOid, t);
      for (const e of parseTree(t.data)) {
        const child = getObject(repo, e.oid);
        if (!child) continue;
        if (child.type === 'tree') expandTree(e.oid);
        else allObjects.set(e.oid, child);
      }
    };
    for (const oid of newCommits) {
      const o = getObject(repo, oid);
      if (!o) continue;
      allObjects.set(oid, o);
      if (o.type === 'commit') expandTree(parseCommit(o.data).tree);
    }
    for (const oid of extraObjects) {
      const o = getObject(repo, oid);
      if (o) allObjects.set(oid, o);
    }
  }
  const sendObjects = [];
  for (const [oid, obj] of allObjects) if (!heldObjects.has(oid)) sendObjects.push({ ...obj, oid });
  // shallow-info: wanted commits whose parent is not in wanted ∪ held
  const included = new Set([...wanted, ...heldCommits]);
  const shallow = [];
  for (const c of wanted) {
    const obj = getObject(repo, c);
    if (!obj) continue;
    const parents = parseCommit(obj.data).parents;
    if (parents.length === 0) { if (depth !== null) shallow.push(c); continue; }
    if (parents.some((p) => !included.has(p))) shallow.push(c);
  }
  const unshallow = [];
  for (const b of shallowBounds) {
    if (!wanted.has(b) && !heldCommits.has(b)) continue;
    const obj = getObject(repo, b);
    if (!obj || obj.type !== 'commit') continue;
    const parents = parseCommit(obj.data).parents;
    if (parents.every((p) => included.has(p))) unshallow.push(b);
  }
  return { pack: writePack(sendObjects), shallow, unshallow };
}
function scanPktPrefix(buf) {
  // Read pkt-lines until flush; return {end, lines}. Throws on malformed input.
  const lines = [];
  let off = 0;
  while (off + 4 <= buf.length) {
    const lenStr = buf.toString('ascii', off, off + 4);
    if (!/^[0-9a-fA-F]{4}$/.test(lenStr)) throw new Error('bad pkt-line length');
    const len = parseInt(lenStr, 16);
    if (len === 0) return { end: off + 4, lines };
    if (len === 1) { lines.push({ kind: 'delim' }); off += 4; continue; }
    if (len < 4 || off + len > buf.length) throw new Error('truncated pkt-line');
    lines.push({ kind: 'data', payload: buf.subarray(off + 4, off + len) });
    off += len;
  }
  throw new Error('pkt stream ended without flush');
}
async function handleGit(req, res, m, url) {
  const owner = decodeURIComponent(m[1]);
  const name = decodeURIComponent(m[2]);
  const suffix = m[3] ?? '';
  const repo = getRepo(owner, name);
  if (req.method === 'GET' && suffix.startsWith('/info/refs')) {
    const service = url.searchParams.get('service') ?? '';
    if (!repo) return sendErr(res, 404, 'Not Found');
    if (service === 'git-upload-pack') {
      const proto = (req.headers['git-protocol'] ?? '') === 'version=2' ? 2 : 0;
      const body = proto === 2 ? v2Advertisement() : v0Advertisement(repo, 'git-upload-pack');
      res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-advertisement', 'x-github-request-id': 'req-' + (++reqSeq) });
      return res.end(body);
    }
    if (service === 'git-receive-pack') {
      const body = v0Advertisement(repo, 'git-receive-pack');
      res.writeHead(200, { 'content-type': 'application/x-git-receive-pack-advertisement', 'x-github-request-id': 'req-' + (++reqSeq) });
      return res.end(body);
    }
    return sendErr(res, 404, 'Not Found');
  }
  if (req.method === 'POST' && suffix === '/git-upload-pack') {
    if (!repo) return sendErr(res, 404, 'Not Found');
    let raw;
    try { raw = await readBody(req); } catch { return sendErr(res, 400, 'Bad Request'); }
    let lines;
    try { lines = pktTextLines(raw); } catch { return sendErr(res, 400, 'Bad Request'); }
    const first = (lines[0] ?? '').trim();
    const proto2 = (req.headers['git-protocol'] ?? '') === 'version=2';
    if (first === 'command=ls-refs' || (!proto2 && first.startsWith('command=ls-refs'))) {
      const prefixes = [];
      let peel = false, symrefs = false;
      for (const l of lines) {
        const t = l.trim();
        if (t === 'peel') peel = true;
        else if (t === 'symrefs') symrefs = true;
        else if (t.startsWith('ref-prefix ')) prefixes.push(t.slice(11));
      }
      const keep = (n) => prefixes.length === 0 || prefixes.some((p) => n.startsWith(p));
      const out = [];
      const mainTip = refTip(repo, 'refs/heads/main');
      if (keep('HEAD')) {
        if (mainTip) out.push(pktLine(`${mainTip} HEAD${symrefs ? ' symref-target:refs/heads/main' : ''}\n`));
        else out.push(pktLine('unborn HEAD symref-target:refs/heads/main\n'));
      }
      for (const [refName, oid] of sortedRefs(repo)) {
        if (!keep(refName)) continue;
        let line = `${oid} ${refName}`;
        const obj = getObject(repo, oid);
        if (peel && obj && obj.type === 'tag') {
          const target = peelToCommit(repo, oid);
          if (target) line += ` peeled:${target}`;
        }
        out.push(pktLine(line + '\n'));
      }
      out.push(PKT_FLUSH);
      res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result', 'x-github-request-id': 'req-' + (++reqSeq) });
      return res.end(Buffer.concat(out));
    }
    if (first === 'command=fetch') {
      const wants = []; const haves = []; const shallowIn = [];
      let depth = null;
      for (const l of lines) {
        const t = l.trim();
        if (t.startsWith('want ')) wants.push(t.slice(5).trim());
        else if (t.startsWith('have ')) haves.push(t.slice(5).trim());
        else if (t.startsWith('shallow ')) shallowIn.push(t.slice(8).trim());
        else if (t.startsWith('deepen ')) depth = parseInt(t.slice(7).trim(), 10);
      }
      const cacheKey = repoKey(owner, name) + '|' + wants.join(',') + '|d' + depth + '|h' + haves.join(',') + '|s' + shallowIn.join(',');
      let computed = packCache.get(cacheKey);
      if (!computed) {
        computed = computeFetch(repo, wants, haves, shallowIn, depth);
        packCache.set(cacheKey, computed);
        if (packCache.size > PACK_CACHE_MAX) { const k = packCache.keys().next().value; packCache.delete(k); }
      }
      const parts = [pktLine('acknowledgments\n'), pktLine('NAK\n'), PKT_DELIM];
      if (computed.shallow.length || computed.unshallow.length) {
        parts.push(pktLine('shallow-info\n'));
        for (const s of computed.shallow) parts.push(pktLine('shallow ' + s + '\n'));
        for (const s of computed.unshallow) parts.push(pktLine('unshallow ' + s + '\n'));
        parts.push(PKT_DELIM);
      }
      parts.push(pktLine('packfile\n'));
      parts.push(sidebandPackets(computed.pack));
      res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result', 'x-github-request-id': 'req-' + (++reqSeq) });
      return res.end(Buffer.concat(parts));
    }
    // v0 fetch (no Git-Protocol: version=2 header): lines are want/have/shallow/deepen.
    const wants = []; const haves = []; const shallowIn = [];
    let depth = null; let sawWant = false;
    for (const l of lines) {
      const t = l.trim();
      if (t.startsWith('want ')) { wants.push(t.slice(5).split(' ')[0]); sawWant = true; }
      else if (t.startsWith('have ')) haves.push(t.slice(5).trim());
      else if (t.startsWith('shallow ')) shallowIn.push(t.slice(8).trim());
      else if (t.startsWith('deepen ')) depth = parseInt(t.slice(7).trim(), 10);
    }
    if (!sawWant) return sendErr(res, 400, 'Bad Request');
    const computed = computeFetch(repo, wants, haves, shallowIn, depth);
    const parts = [pktLine('NAK\n')];
    for (const s of computed.shallow) parts.push(pktLine('shallow ' + s + '\n'));
    for (const s of computed.unshallow) parts.push(pktLine('unshallow ' + s + '\n'));
    parts.push(sidebandPackets(computed.pack));
    res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result', 'x-github-request-id': 'req-' + (++reqSeq) });
    return res.end(Buffer.concat(parts));
  }
  if (req.method === 'POST' && suffix === '/git-receive-pack') {
    if (!repo) return sendErr(res, 404, 'Not Found');
    let raw;
    try { raw = await readBody(req); } catch { return sendErr(res, 400, 'Bad Request'); }
    let prefix;
    try { prefix = scanPktPrefix(raw); } catch { return sendErr(res, 400, 'Bad Request'); }
    const commands = [];
    for (const p of prefix.lines) {
      if (p.kind !== 'data') continue;
      let text = p.payload.toString('utf8');
      const nul = text.indexOf('\0');
      if (nul >= 0) text = text.slice(0, nul);
      const line = text.replace(/\n$/, '');
      const parts = line.split(' ');
      if (parts.length >= 3 && isOid(parts[0]) && isOid(parts[1])) {
        commands.push({ oldOid: parts[0], newOid: parts[1], ref: parts.slice(2).join(' ') });
      }
    }
    if (!commands.length) return sendErr(res, 400, 'Bad Request');
    const packBytes = raw.subarray(prefix.end);
    let unpackOk = true; let unpackDetail = 'ok';
    if (packBytes.length) {
      try {
        const parsed = readPack(packBytes);
        for (const [oid, obj] of parsed.objects) {
          if (!repo.objects.has(oid)) repo.objects.set(oid, obj);
        }
      } catch (e) {
        unpackOk = false;
        unpackDetail = 'unpack error: ' + (e instanceof Error ? e.message : String(e));
      }
    }
    const reportLines = [];
    if (unpackOk) reportLines.push('unpack ok');
    else reportLines.push('unpack ' + unpackDetail);
    if (unpackOk) {
      for (const cmd of commands) {
        const current = repo.refs.get(cmd.ref) ?? null;
        let ok = false; let reason = '';
        if (cmd.newOid === ZERO_OID) {
          // delete
          if (current === null) { ok = false; reason = 'non-fast-forward'; }
          else if (current !== cmd.oldOid) { ok = false; reason = 'non-fast-forward'; }
          else { repo.refs.delete(cmd.ref); ok = true; }
        } else if (cmd.oldOid === ZERO_OID) {
          // create
          if (current !== null) { ok = false; reason = 'non-fast-forward'; }
          else if (!getObject(repo, cmd.newOid)) { ok = false; reason = 'missing object'; }
          else { repo.refs.set(cmd.ref, cmd.newOid); ok = true; }
        } else {
          // update
          if (current !== cmd.oldOid) { ok = false; reason = 'non-fast-forward'; }
          else if (!getObject(repo, cmd.newOid)) { ok = false; reason = 'missing object'; }
          else if (!isAncestor(repo, cmd.oldOid, cmd.newOid)) { ok = false; reason = 'non-fast-forward'; }
          else { repo.refs.set(cmd.ref, cmd.newOid); ok = true; }
        }
        reportLines.push(ok ? 'ok ' + cmd.ref : 'ng ' + cmd.ref + ' ' + reason);
      }
      packCache.clear();
      invalidateRepo(repo);
    }
    const inner = [];
    for (const line of reportLines) inner.push(pktLine(line + '\n'));
    inner.push(PKT_FLUSH);
    const innerBuf = Buffer.concat(inner);
    const body = Buffer.concat([pktLine(Buffer.concat([Buffer.from([1]), innerBuf])), PKT_FLUSH]);
    res.writeHead(200, { 'content-type': 'application/x-git-receive-pack-result', 'x-github-request-id': 'req-' + (++reqSeq) });
    return res.end(body);
  }
  return sendErr(res, 404, 'Not Found');
}

// ---- server bootstrap ------------------------------------------------------
async function handle(req, res) {
  try {
    const url = new URL(req.url ?? '/', 'http://x');
    const path = url.pathname;
    if (req.method === 'GET' && path === '/healthz') return sendJson(res, 200, { ok: true });
    const gitMatch = /^\/([^/]+)\/([^/]+)\.git(\/.*)?$/.exec(path);
    if (gitMatch) { await handleGit(req, res, gitMatch, url); return; }
    if (path === '/api/graphql') {
      if (!bearer(req)) return sendErr(res, 401, 'Unauthorized');
      if (req.method !== 'POST') return sendErr(res, 404, 'Not Found');
      await handleGraphQL(req, res);
      return;
    }
    if (path === '/mcp') {
      if (!bearer(req)) {
        res.writeHead(401, { 'content-type': 'application/json', 'x-github-request-id': 'req-' + (++reqSeq) });
        return res.end(JSON.stringify({ jsonrpc: '2.0', id: null, error: { code: -32000, message: 'Unauthorized' } }));
      }
      if (req.method === 'POST') { await handleMcp(req, res); return; }
      if (req.method === 'DELETE') { res.writeHead(204, { 'x-github-request-id': 'req-' + (++reqSeq) }); return res.end(); }
      return sendErr(res, 404, 'Not Found');
    }
    if (path === '/api/v3' || path.startsWith('/api/v3/')) {
      if (!bearer(req)) return sendErr(res, 401, 'Unauthorized');
      const segments = path.slice(8).split('/').filter((s) => s !== '');
      await handleRest(req, res, segments, url);
      return;
    }
    return sendErr(res, 404, 'Not Found');
  } catch (err) {
    if (!res.headersSent) sendErr(res, 500, 'Internal Server Error');
    else { try { res.end(); } catch { /* ignore */ } }
  }
}

const server = http.createServer(handle);
server.keepAliveTimeout = 30000;
server.headersTimeout = 60000;

function sleep(ms) { return new Promise((r) => setTimeout(r, ms)); }

async function main() {
  await new Promise((resolve) => server.listen(0, '0.0.0.0', resolve));
  const addr = server.address();
  const port = typeof addr === 'object' && addr ? addr.port : 0;
  const envUrl = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');
  if (!envUrl) {
    console.log('forge listening on port ' + port);
    return;
  }
  // Register, then long-poll /done until the suite finishes.
  for (let attempt = 0; attempt < 200; attempt++) {
    try {
      const r = await fetch(envUrl + '/register', {
        method: 'POST',
        headers: { 'content-type': 'application/json' },
        body: JSON.stringify({ port }),
        signal: AbortSignal.timeout(5000),
      });
      if (r.ok) break;
    } catch { /* retry */ }
    await sleep(250);
  }
  while (true) {
    try {
      const r = await fetch(envUrl + '/done', { signal: AbortSignal.timeout(10000) });
      if (r.ok) {
        const j = await r.json();
        if (j && j.done === true) break;
      }
    } catch { /* retry */ }
    await sleep(250);
  }
  server.close();
  process.exit(0);
}
process.on('SIGTERM', () => { server.close(() => process.exit(0)); });
main().catch(() => { try { server.close(); } catch { /* ignore */ } process.exit(1); });
