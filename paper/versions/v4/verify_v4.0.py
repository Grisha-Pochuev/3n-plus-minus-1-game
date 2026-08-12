#!/usr/bin/env python3
"""Supporting arithmetic and finite control checks for the v3.0 article.

The script checks exact identities used in the text and the acyclicity of the
finite equal-rank control graph.  It is supporting verification, not an
end-to-end proof of the infinite theorem.
"""
from __future__ import annotations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def A(q: int) -> int:
    return (3*q + 1)//2


def asl(n: int) -> int:
    if n == 0:
        return 0
    bits = bin(n)[2:]
    k = 1
    i = len(bits)-1
    while i > 0 and bits[i-1] != bits[i]:
        k += 1
        i -= 1
    return k


def R(n: int) -> int:
    return n >> asl(n)


def B(q: int) -> int:
    return R(A(q))


def Q(r: int, e: int, a: int) -> int:
    return a*(1 << r)-e


def J(s: int) -> int:
    return 2*A(s)+1


def alpha(s: int) -> int:
    return 1-((s//2) % 2)


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length()-1


def oddpart(n: int) -> int:
    return n >> v2(n)



def kappa(q: int) -> int:
    assert q > 0
    if q % 2 == 0:
        return oddpart(q)
    return oddpart(q+1)


def check_coefficient_pullback(limit=100000):
    for w in range(1,limit+1,2):
        assert kappa(3*w)==J(R(w))
        assert kappa(3*w-1)==J(R(2*w-1))



def check_source_boundary(limit=200000):
    for s in range(1, limit+1):
        e=alpha(s)
        n=3*J(s)+1-2*e
        assert v2(n)==1
        assert oddpart(n)==J(A(s))
        n2=3*J(s)+1-2*(1-e)
        assert v2(n2)>=2
        assert oddpart(n2)==J(B(s))


def constant_tail_coordinates(q: int):
    assert q>0
    if q%2==0:
        r=v2(q); return oddpart(q),r,0
    r=v2(q+1); return oddpart(q+1),r,1


def source_of_odd_coeff(a: int) -> int:
    while a%3==0:
        a//=3
    # invert J by binary search; J is strictly increasing
    lo,hi=0,max(1,a)
    while lo<=hi:
        m=(lo+hi)//2; jm=J(m)
        if jm==a: return m
        if jm<a: lo=m+1
        else: hi=m-1
    raise AssertionError(('not J image',a))


def rho(q: int) -> int:
    a,_,_=constant_tail_coordinates(q)
    return source_of_odd_coeff(a)


def check_boundary_coefficient(limit=100000):
    for a in range(1,limit+1,2):
        for e in (0,1):
            p=B(Q(1,e,a))
            assert p==B(Q(2,e,a))
            if p>0:
                kp=constant_tail_coordinates(p)[0]
                assert 4*kp <= 3*a+1
                if a>=3: assert kp<a
                assert 6*rho(p) <= p-1


def check_a_side(limit=200000):
    for x in range(1,limit+1):
        e=alpha(x); w=Q(1,e,J(x)); y=A(x)
        assert B(w) in (A(y),B(y))


def check_b_transfer_diamond(limit=200000):
    for x in range(1,limit+1):
        e=1-alpha(x); a=J(x); g=1-e
        n=3*a+1-2*e; j=v2(n); y=B(x)
        assert j>=2 and oddpart(n)==J(y)
        P=Q(1,e,a); U=Q(2,e,a)
        D=Q(j,g,J(y)); C=Q(j-1,g,J(y)); F=A(U)
        assert D==A(P) and C==B(P) and C==B(U)
        md={A(D),B(D)}; mc={A(C),B(C)}
        common=md & mc
        assert len(common)==1
        X=next(iter(common)); other=mc-{X}
        assert len(other)==1
        Y=next(iter(other))
        assert B(F)==Y


def check_long_tail(limit=20001, max_r=18):
    for a in range(1, limit+1, 2):
        for e in (0,1):
            for r in range(3,max_r+1):
                assert A(Q(r,e,a)) == Q(r-1,e,3*a)
                assert B(Q(r,e,a)) == Q(r-2,e,3*a)
            assert B(Q(1,e,a)) == B(Q(2,e,a))


def check_fixed_tail_diamond(limit=20001, max_r=18):
    for c in range(1,limit+1,2):
        for e in (0,1):
            for r in range(2,max_r+1):
                X=Q(r,e,3*c); G=Q(r,e,c); H=Q(r+1,e,c); Y=A(G)
                assert A(H)==X
                assert B(H)==Y
                if r==2:
                    assert B(X)==B(Y)
                elif r==3:
                    assert B(X)==A(Y)
                else:
                    assert B(X)==A(Y)


def check_side_relation(limit=100000):
    exc={1,3,12,14}
    for q in range(1,limit+1):
        if q%16 not in exc:
            t=B(A(q)); s=B(q)
            assert t in (A(s), B(s)), (q,s,t,A(s),B(s))
        if q%16 in exc:
            assert A(q)%16 not in exc


def check_base_entry(limit=200000):
    for x in range(1,limit+1):
        a=J(x)
        for e in (0,1):
            P=Q(1,e,a); U=Q(2,e,a); b=B(P)
            assert b==B(U)
            n=9*a+1-2*e
            v=v2(n); g=1-e
            assert oddpart(n)==J(b)
            if e==1-alpha(x):
                assert v==1
                assert b==3*A(x)+1
                T=Q(1,g,J(b)); C=R(T)
                assert C in (A(b),B(b))
            else:
                assert e==alpha(x)
                assert v>=2
                if v>=4:
                    assert b<x
                if v==3:
                    assert J(b)%3==(1+g)%3


def check_zero_source_valuations(max_n=200):
    for n in range(1,max_n+1):
        jplus=v2(3**n+1)
        jminus=v2(3**n-1)
        assert jplus==(2 if n%2 else 1)
        assert jminus==(1 if n%2 else 2+v2(n))
        for e in (0,1):
            N=3**n+1-2*e
            j=v2(N); b=oddpart(N)
            if j==1:
                y=(3**(n-1)-1)//2
                assert b==J(y)
                if e==0:
                    assert R(3**n)==A(y)
                else:
                    assert R(3**n-1)==B(y)





def check_alternating_lift(limit=200000):
    for z in range(1, limit+1):
        delta=1-(z%2)
        r=R(z)
        target=3*z+1
        found=False
        # the theorem gives an exact finite constant-tail exponent
        for m in range(1, max(3, z.bit_length()+2)):
            if Q(m,delta,J(r))==target:
                found=True
                break
        assert found, (z,r,delta,target)


def check_exceptional_side(limit=200000):
    exc={1,3,12,14}
    for q in range(1, limit+1):
        if q%16 not in exc:
            continue
        ell=B(q); p=B(A(q)); v=A(A(q))
        # p is an exact lift over ell and v the adjacent lift.
        delta=(v-2*p)
        assert delta in (0,1), (q,p,v)
        found=False
        for m in range(1, max(3, p.bit_length()+2)):
            if p==Q(m,delta,J(ell)) and v==Q(m+1,delta,J(ell)):
                found=True; break
        assert found, (q,ell,p,v,delta)

def check_hidden_parent(limit_a=20000):
    for a in range(1,limit_a+1,2):
        if a%3==0:
            continue
        for e in (0,1):
            if a%3 != (1+e)%3:
                continue
            H=Q(3,e,a); G=Q(2,e,a)
            num=2*H+e-1
            assert num%3==0
            K=num//3
            assert A(K)==H
            assert B(K)==G

def check_control_dag():
    data=json.loads((ROOT/'routing_certificate_v3_0.json').read_text())
    controls=set(data['controls'])
    edges=data['equal_rank_edges']
    adj={v:[] for v in controls}
    indeg={v:0 for v in controls}
    for u,v in edges:
        assert u in controls and v in controls
        adj[u].append(v); indeg[v]+=1
    stack=[v for v,d in indeg.items() if d==0]
    seen=[]
    while stack:
        u=stack.pop(); seen.append(u)
        for v in adj[u]:
            indeg[v]-=1
            if indeg[v]==0: stack.append(v)
    assert len(seen)==len(controls), 'equal-rank control graph contains a cycle'
    # Longest remaining equal-rank path is a concrete finite control rank.
    order=seen[::-1]
    rank={v:0 for v in controls}
    for u in order:
        if adj[u]: rank[u]=1+max(rank[v] for v in adj[u])
    for u,v in edges:
        assert rank[u]>rank[v]
    expected={
      'marked_tail':9,'boundary_entry':8,'short_lift':8,'a_obligation':7,
      'a_test_4':6,'a_test_3':5,'a_test_2':4,'a_test_1':3,
      'b_select':2,'loss_sibling_entry':2,'b2_first':1,'factor_fork':1,
      'b2_ready':0,'high_return':0,'terminal_macro':0}
    assert rank==expected, (rank,expected)
    return rank


def main():
    check_source_boundary()
    check_coefficient_pullback()
    check_boundary_coefficient()
    check_a_side()
    check_b_transfer_diamond()
    check_long_tail()
    check_fixed_tail_diamond()
    check_side_relation()
    check_base_entry()
    check_zero_source_valuations()
    check_alternating_lift()
    check_exceptional_side()
    check_hidden_parent()
    rank=check_control_dag()
    print('v3.0 supporting checks passed')
    print('maximum equal-rank control height:', max(rank.values()))


if __name__=='__main__':
    main()
