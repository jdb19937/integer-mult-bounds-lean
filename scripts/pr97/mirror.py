"""Python transcription of the checks in M8/Local/Kernel.lean, on the records emit_lean.py writes."""
import json, sys
from itertools import combinations
sys.set_int_max_str_digits(0)
import emit_lean as E
H=23; TRIP=E.TRIP; TID=E.TID
def bit(k): return 1<<k
def pb(u,w): return 23*u+w if u<w else 23*w+u
def testB(m,k): return (m>>k)&1==1
def subB(S,T): return S&T==S
def disj(a,b,c): return a&b==0 and a|b==c
diag=sum(1<<(23*z) for z in range(23)); sm=sum(1<<(22*j) for j in range(23))
allP=sum(1<<pb(u,w) for u in range(23) for w in range(u+1,23))
def spread(X): return (X*sm)&diag
def starMask(o,Z): return ((Z>>(o+1))<<(24*o+1))|(spread(Z&(bit(o)-1))<<o)
def touch(u): return ((0x7fffff>>(u+1))<<(24*u+1))|(spread(bit(u)-1)<<u)
def pairsWithout(c): return allP^(allP&touch(c))
def validZ(x,y): return 0x7fffff^bit(x)^bit(y)
def relP(c,s):
    if s[0]=='three':
        _,p0,p1,p2=s
        if c==p0: return bit(pb(p1,p2))
        if c==p1: return bit(pb(p0,p2))
        if c==p2: return bit(pb(p0,p1))
        return None
    if s[0]=='two':
        _,x,y,Z=s
        if c==x: return starMask(y,Z)
        if c==y: return starMask(x,Z)
        return None
    return s[2] if c==s[1] else None
def relZ(x,y,s):
    if s[0]=='three':
        _,p0,p1,p2=s
        if (x,y)==(p0,p1): return bit(p2)
        if (x,y)==(p0,p2): return bit(p1)
        if (x,y)==(p1,p2): return bit(p0)
        return None
    if s[0]=='two': return s[3] if (x,y)==(s[1],s[2]) else None
    return None
def optU(a,b,c): return a is not None and b is not None and disj(a,b,c)
def supportOk(s,sa,sb):
    if s[0]=='two':
        _,x,y,Z=s; return x<y<23 and subB(Z,validZ(x,y)) and optU(relZ(x,y,sa),relZ(x,y,sb),Z)
    if s[0]=='one':
        _,c,P=s; return c<23 and subB(P,pairsWithout(c)) and optU(relP(c,sa),relP(c,sb),P)
    return False
def points3(s): return s[1:4] if s[0]=='three' else (0,0,0)
def nodeOk(R,n,r):
    if n<1771:
        s=r['supp']
        ok=(not r['isAdd']) and s[0]=='three' and s[1]<s[2]<s[3]<23
        return ok and (n==0 or points3(R[n-1]['supp'])<points3(s))
    return r['isAdd'] and r['a']<n and r['b']<n and supportOk(r['supp'],R[r['a']]['supp'],R[r['b']]['supp'])
def arg(r,pos): return r['b'] if pos else r['a']
def donor(r,pos): return r['d1'] if pos else r['d0']
def spanOk(L,s,st):
    if not L['paths']:
        pts=list(st[1:4]) if st[0]=='three' else (list(st[1:3]) if st[0]=='two' else [st[1]])
        for c in pts:
            pn,pt=relP(c,s),relP(c,st)
            if pn is not None and pt is not None and subB(pn,pt): return True
        return False
    c=L['point']; pn,pt=relP(c,s),relP(c,st)
    if pn is None or pt is None: return False
    ends=0
    for (u,x,y,w) in L['paths']:
        if c in (u,x,y,w) or u==x or x==y or y==w or u==w or max(u,x,y,w)>=23: return False
        if not (testB(pt,pb(u,x)) and testB(pt,pb(x,y)) and testB(pt,pb(y,w))): return False
        ends|=bit(pb(u,w))
    return (pn^(pn&pt))==ends
def linkOk(R,n,r):
    L=r['link']
    if L is None: return True
    rt=R[L['user']] if L['user']<len(R) else None
    return r['isAdd'] and n<L['user']<64042 and rt['isAdd'] and arg(rt,L['pos'])==arg(r,L['operand']) and donor(rt,L['pos'])==n and spanOk(L,r['supp'],rt['supp'])
def donorOk(R,n,pos,d):
    if d is None: return True
    L=R[d]['link']
    return d<64042 and L is not None and L['user']==n and L['pos']==pos
def freeOk(R,roots,n,r):
    f=r['free']
    if f[0]=='gate':
        u,pos=f[1],f[2]; ru=R[u]
        return n<u<64042 and ru['isAdd'] and arg(ru,pos)==n and donor(ru,pos) is None
    return f[1]<5336 and roots[f[1]]['node']==n
def rootOk(R,j,q):
    if not (q['node']<64042 and q['c']<23): return False
    M=relP(q['c'],R[q['node']]['supp'])
    if M is None: return False
    if q['out'] is not None:
        a,b=q['out']; c=q['c']
        if not (j<3*1771 and a<b<23 and a!=c and b!=c): return False
        s=R[j//3]['supp']
        if s[0]!='three': return False
        p0,p1,p2=s[1:4]
        ok=(c==p0 and a==p1 and b==p2 and j%3==0) or (c==p1 and a==p0 and b==p2 and j%3==1) or (c==p2 and a==p0 and b==p1 and j%3==2)
        return ok and M==(pairsWithout(c)^(pairsWithout(c)&(touch(a)|touch(b))))
    return j==3*1771+q['c'] and M==pairsWithout(q['c'])
D=json.load(open(sys.argv[1]))
roots=[None]*(3*1771+23)
for q in D['roots']:
    if 'out' in q:
        c,T=q['out']; j=3*TID[tuple(T)]+T.index(c); a,b=[x for x in T if x!=c]
        roots[j]={'node':q['node'],'c':c,'out':(a,b),'key':('out',c,tuple(T))}
    else:
        j=3*1771+q['ret']; roots[j]={'node':q['node'],'c':q['ret'],'out':None,'key':('ret',q['ret'])}
ridx={q['key']:j for j,q in enumerate(roots)}
R=[]
for rec in D['nodes']:
    L=rec.get('link')
    sp=rec['supp']
    if sp[0]=='leaf': s=('three',)+TRIP[sp[1]]
    elif sp[0]=='two': s=('two',sp[1],sp[2],sp[3])
    else: s=('one',sp[1],E.pmask_23(sp[1],sp[2]))
    f=rec['free']
    if f[0]=='gate': fr=('gate',f[1],f[2]==1)
    else: fr=('root',ridx[('out',f[1],tuple(f[2])) if f[0]=='out' else ('ret',f[1])])
    lf=rec.get('linkedFrom',{})
    R.append({'isAdd':'args' in rec,'a':rec['args'][0] if 'args' in rec else 0,'b':rec['args'][1] if 'args' in rec else 0,
      'link':None if L is None else {'operand':L['operand']==1,'user':L['user'],'pos':L['pos']==1,'point':L.get('point',0),'paths':[tuple(p) for p in L.get('relations',[])]},
      'd0':lf.get('0'),'d1':lf.get('1'),'free':fr,'supp':s})
bad=[n for n,r in enumerate(R) if not (nodeOk(R,n,r) and linkOk(R,n,r) and donorOk(R,n,False,r['d0']) and donorOk(R,n,True,r['d1']) and freeOk(R,roots,n,r))]
print('node failures',len(bad),bad[:5])
rb=[j for j,q in enumerate(roots) if not rootOk(R,j,q)]
print('root failures',len(rb),rb[:5])
