#!/usr/bin/env python3
"""Table-driven rename for the final series (see design/NAMES.md).

usage: rename.py NAMES.tsv ASYNC_DIR [--apply] [--git]

NAMES.tsv rows (tab-separated; '#' comments):
  theory  OLD  NEW            theory OLD (file OLDScript.sml) becomes NEW
  lib     OLD  NEW            ML library OLD (file OLD.sml) becomes NEW
  const   OLD  NEW  exact     the token OLD becomes NEW
  const   OLD  NEW  prefix    also OLD_xxx becomes NEW_xxx (derived names: _def, _ind, _thm, ...)

Theory renames apply in code and comments, XTheory and X$c, and in a
string that is exactly one name ("X" in translation_extends / fetch).
Other string contents are data (e.g. a served file) and are never changed.  Constant renames apply
outside ML string literals (except a string that is exactly one name, e.g.
new_definition ("old_def", ...)), outside «mlstring» literals and outside
Quote add_cakeml ... End blocks (CakeML source is never changed).
Markdown files get both maps, except the numbered design notes
(design/NN-*.md), which are kept as written (NAMES.md maps them).
Without --apply: report what would change, and check collisions.

NOT IDEMPOTENT: the table has swap chains (HttpSpec -> HttpGetSpec while
HttpSpecBodies -> HttpSpec), so run it once per file.  On a partially
renamed tree (a stack renamed layer by layer), pass only the directories
the new layer adds.  The tool refuses a tree that already contains a
renamed theory (a NEW name that is not also an OLD name).
"""
import os, re, sys, subprocess
TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

def load(p):
    th, ce = {}, []
    for line in open(p):
        line = line.split('#', 1)[0].rstrip('\n')
        if not line.strip(): continue
        f = line.split('\t')
        if f[0] in ('theory', 'lib'): th[f[1]] = f[2]
        elif f[0] == 'const': ce.append((f[1], f[2], f[3] if len(f) > 3 else 'exact'))
        else: sys.exit('bad row: ' + line)
    return th, ce

def map_token(t, th, cexact, cpref, consts=True):
    if "'" in t and not t.startswith("'"):          # possessives in comments: asyncFoo's
        i = t.index("'")
        return map_token(t[:i], th, cexact, cpref, consts) + t[i:]
    if t in th: return th[t]
    if t.endswith('Theory') and t[:-6] in th: return th[t[:-6]] + 'Theory'
    if t[:1].isupper() and '_' in t:                 # translator names: ASYNCPROTO_PRESULT_TYPE(_def)
        for old, new in th.items():
            if old.upper() != old and t.startswith(old.upper() + '_'):
                return new.upper() + t[len(old):]
    if not consts: return t
    if t in cexact: return cexact[t]
    for old, new in cpref:
        if t == old: return new
        if t.startswith(old + '_'): return new + t[len(old):]
    return t

def segments(s):
    """Split SML source into (kind, text): kind 'code', 'str' ("..."), 'mlstr' («...»), 'quote' (Quote ... End)."""
    out, i, n = [], 0, len(s)
    buf = []
    def flush():
        if buf: out.append(('code', ''.join(buf))); buf.clear()
    while i < n:
        if s.startswith('Quote ', i) and (i == 0 or s[i-1] == '\n'):
            j = s.find('\nEnd', i)
            j = n if j < 0 else j + 4
            flush(); out.append(('quote', s[i:j])); i = j; continue
        c = s[i]
        if c == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            flush(); out.append(('str', s[i:j+1])); i = j + 1; continue
        if c == '«':
            j = s.find('»', i)
            j = n if j < 0 else j + 1
            flush(); out.append(('mlstr', s[i:j])); i = j; continue
        buf.append(c); i += 1
    flush()
    return out

def rewrite(s, th, cexact, cpref, md=False):
    def sub(text, consts):
        return TOK.sub(lambda m: map_token(m.group(0), th, cexact, cpref, consts), text)
    if md:
        return sub(s, True)
    res = []
    for kind, text in segments(s):
        if kind == 'code': res.append(sub(text, True))
        elif kind == 'str':
            inner = text[1:-1]
            if TOK.fullmatch(inner):                         # "name_def", fetch "-" "x": a name
                res.append('"' + map_token(inner, th, cexact, cpref, True) + '"')
            else:
                res.append(text)                             # string contents are data: untouched
        else: res.append(text)                               # «...», Quote blocks: untouched
    return ''.join(res)

def main():
    names, root = sys.argv[1], sys.argv[2]
    apply_, git = '--apply' in sys.argv, '--git' in sys.argv
    th, ce = load(names)
    cexact = {o: n for o, n, m in ce if m == 'exact'}
    cpref = sorted([(o, n) for o, n, m in ce if m == 'prefix'], key=lambda x: -len(x[0]))
    files = []
    for d, _, fs in os.walk(root):
        if '/.hol' in d or d.endswith('.hol'): continue
        for f in fs:
            if f.endswith(('.sml', '.md')) : files.append(os.path.join(d, f))
    # existing theory names and tokens, for collision checks
    existing = {os.path.basename(f)[:-10] for f in files if f.endswith('Script.sml')}
    libs = {os.path.basename(f)[:-4] for f in files if f.endswith('.sml')}
    already = sorted(t for t in existing if t in set(th.values()) and t not in th)
    if already:
        sys.exit('REFUSED: already renamed here (pass only unrenamed directories): ' + ' '.join(already[:8]))
    missing = [t for t in th if t not in existing and t not in libs]
    if missing: print('WARNING: theories in the table but not in the tree:', ' '.join(missing))
    newth = [th.get(t, t) for t in existing]
    dup = {x for x in newth if newth.count(x) > 1}
    if dup: sys.exit('COLLISION: theory names ' + ' '.join(sorted(dup)))
    alltok = set()
    for f in files:
        if f.endswith('.sml'): alltok |= set(TOK.findall(open(f, encoding='utf-8').read()))
    for o, n, m in ce:
        if n in alltok and n not in {x for x, _, _ in ce}:
            print('WARNING: new constant name already used in the tree:', n, '(from', o + ')')
    changed = 0
    moves = []                      # two-phase, so that swaps (A->B, B->C) work
    for f in sorted(files):
        base = os.path.basename(f)
        md = f.endswith('.md')
        if md and re.match(r'\d\d-', base) and '/design/' in f: continue
        if base in ('NAMES.md',): continue                 # the table itself
        s = open(f, encoding='utf-8').read()
        t = rewrite(s, th, cexact, cpref, md)
        nf = f
        if base.endswith('Script.sml') and base[:-10] in th:
            nf = os.path.join(os.path.dirname(f), th[base[:-10]] + 'Script.sml')
        elif base.endswith('.sml') and base[:-4] in th:
            nf = os.path.join(os.path.dirname(f), th[base[:-4]] + '.sml')
        if t != s or nf != f:
            changed += 1
            if not apply_:
                print(('MOVE ' + f + ' -> ' + nf) if nf != f else ('EDIT ' + f))
            else:
                if nf != f:
                    tmp = nf + '.renaming'
                    if git: subprocess.run(['git', 'mv', f, tmp], check=True)
                    else: os.rename(f, tmp)
                    moves.append((tmp, nf))
                    open(tmp, 'w', encoding='utf-8').write(t)
                else:
                    open(nf, 'w', encoding='utf-8').write(t)
    for tmp, nf in moves:
        if git: subprocess.run(['git', 'mv', tmp, nf], check=True)
        else: os.rename(tmp, nf)
    print(changed, 'files', 'changed' if apply_ else 'would change')

if __name__ == '__main__':
    main()
