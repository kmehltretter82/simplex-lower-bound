"""Independent Figure 2 game evaluator, for semantic auditing only.

Enumerates every opponent choice at F vertices and evaluates actual eventual
cycles. No LP reward formula is used by the parity-game evaluator.
"""
from itertools import product
import sys
from cunningham_numeric import data, solve


def game(n):
    decisions = [(k, i) for k, indices in [
        ('a', range(2, n+1)), ('b', range(2, n)),
        ('c', range(2, n+1)), ('d', range(2, n+1)),
        ('e', range(1, n+1))] for i in indices]
    nodes = decisions + [(k, i) for k in 'Fgh' for i in range(1,n+1)] + [('s',0),('t',0)]
    priority = lambda v: {'a':3,'b':3,'c':3,'d':5,'e':5,'F':6,'g':2*v[1]+7,'h':2*v[1]+8,'s':8,'t':1}[v[0]]
    def decision(k,i):
        if k == 'a' and i == n+1: return ('t',0)
        if k in 'bc' and i == 1: return ('g',1)
        return (k,i)
    def targets(v):
        k,i=v
        if k=='a': return [decision('a',i+1),('g',i)]
        if k in 'bd': return [decision('b',i-1),(('g' if k=='b' else 'F'),i)]
        if k=='c': return [decision('c',i-1),('g',i)]
        if k=='e': return [('s',0),('F',i)]
        if k=='F': return [('h',i),('e',i)] + ([('d',i)] if i>1 else [])
        if k=='g': return [('F',i)]
        if k=='h': return [decision('a',i+1)]
        if k=='s': return [('c',n)]
        return [('t',0)]
    return decisions,nodes,priority,targets


def parity_trace(n):
    rows,nodes,priority,targets=game(n)
    _,columns,_,_,_=data(n,'reward')
    sigma={v: targets(v)[int(v[0]=='d' or v==('e',1))] for v in rows}
    fixed={v:targets(v)[0] for v in nodes if v not in sigma}
    opponent=list(product(*(targets(('F',i)) for i in range(1,n+1))))
    def values():
        best={}
        for choices in opponent:
            succ={**fixed,**sigma,**{('F',i+1):v for i,v in enumerate(choices)}}
            for v in nodes:
                path=[]; seen={}; w=v
                while w not in seen:
                    seen[w]=len(path); path.append(w); w=succ[w]
                cycle=path[seen[w]:]
                p=max(map(priority,cycle))
                leaders=[u for u in cycle if priority(u)==p]
                assert len(leaders)==1, (n,cycle,p)
                length=seen[leaders[0]]
                counts=[sum(priority(u)==q for u in path[:length]) if q>p else 0 for q in range(2*n+8,0,-1)]
                val=(p if p%2==0 else -p,*(c if q%2==0 else -c for c,q in zip(counts,range(2*n+8,0,-1))),length if p%2 else -length)
                if v not in best or val<best[v]: best[v]=val
        return best
    last=0; trace=[]
    while True:
        val=values()
        improving=[j for j,(k,i,b) in enumerate(columns) if val[sigma[(k,i)]]<val[targets((k,i))[b]]]
        if not improving: return trace
        j=min(improving,key=lambda j:(j-last)%len(columns))
        k,i,b=columns[j]; sigma[(k,i)]=targets((k,i))[b]
        trace.append((k,i,b)); last=j
        assert len(trace)<10000


def simplex_trace(n):
    rows,columns,A,c,basis=data(n,'reward')
    last=0; trace=[]
    while True:
        mat=[[row[j] for j in basis] for row in A]
        values=solve(mat,[1]*len(rows))
        dual=solve(list(map(list,zip(*mat))),[c[j] for j in basis])
        rc=[c[j]-sum(y*row[j] for y,row in zip(dual,A)) for j in range(len(columns))]
        candidates=[j for j in range(len(columns)) if j not in basis and rc[j]>0]
        if not candidates: return trace
        j=min(candidates,key=lambda j:(j-last)%len(columns))
        d=solve(mat,[row[j] for row in A])
        ratios=[(values[i]/d[i],i) for i in range(len(rows)) if d[i]>0]
        ratio,l=min(ratios)
        assert sum(r==ratio for r,_ in ratios)==1
        basis[l]=j; last=j; trace.append(columns[j])


if __name__=='__main__':
    for n in map(int,sys.argv[1:] or [3,4]):
        pg=parity_trace(n); lp=simplex_trace(n)
        assert pg==lp,(n,pg,lp)
        print({'n':n,'parity_switches':len(pg),'simplex_pivots':len(lp),'full_action_sequence_equal':True},flush=True)
