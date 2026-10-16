import re,glob,os,sys
A=os.getcwd()+'/'  # run inside async/
files=glob.glob(A+'**/*Script.sml',recursive=True)
loc={os.path.basename(f)[:-10]:os.path.dirname(f)[len(A):] for f in files}
dep={}
for f in files:
    s=open(f).read(); t=os.path.basename(f)[:-10]
    m=re.search(r'\nAncestors\s*\n(.*?)\nLibs',s,re.S)
    anc=set(m.group(1).split()) if m else set()
    anc|=set(re.findall(r'(\w+)Theory\.',s))
    dep[t]={a for a in anc if a in loc and a!=t}
def clos(ts):
    seen=set(); st=list(ts)
    while st:
        a=st.pop()
        if a in seen: continue
        seen.add(a); st+=dep[a]
    return seen
dirs=sys.argv[1].split(',')
extra=dict(x.split('=',1) for x in sys.argv[2:])
for d in dirs:
    ts=[t for t,l in loc.items() if l==d]
    inc=sorted({loc[a] for a in clos({x for t in ts for x in dep[t]})}-{d})
    depth=d.count('/')+1
    rel=[os.path.relpath(A+i,A+d) for i in inc]
    ex=extra.get(d,'$(CAKEMLDIR)/semantics').split()
    lines=rel+ex
    hdr=open(A+d+'/Holmakefile.hdr').read() if os.path.exists(A+d+'/Holmakefile.hdr') else ''
    out=hdr+'INCLUDES = '+' \\\n           '.join(lines)+'\nifdef POLY\nHOLHEAP = $(CAKEMLDIR)/basis/basis-heap\nendif\n'
    open(A+d+'/Holmakefile','w').write(out)
    print(d, len(inc))
# cycle check among dirs
dd={}
for t,l in loc.items():
    for a in dep[t]:
        if loc[a]!=l: dd.setdefault(l,set()).add(loc[a])
def cyc(n,stack,vis):
    if n in stack: print('CYCLE',stack[stack.index(n):]); return
    if n in vis: return
    vis.add(n)
    for m in dd.get(n,()): cyc(m,stack+[n],vis)
v=set()
for n in dd: cyc(n,[],v)
