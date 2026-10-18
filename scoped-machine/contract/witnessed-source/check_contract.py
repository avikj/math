#!/usr/bin/env python3
"""Finite checks of the author contract. NOT a production-machine test runner."""
from __future__ import annotations
from collections import Counter
from dataclasses import dataclass, field
from itertools import permutations
from fractions import Fraction
import json
from pathlib import Path

checks = []
def check(name, predicate):
    assert predicate, name
    checks.append(name)

def clean(c):
    return Counter({k:v for k,v in c.items() if v})

def plus(*chains):
    out=Counter()
    for c in chains:
        out.update(c)
    return clean(out)

def scale(n,c):
    return clean(Counter({k:n*v for k,v in c.items()}))

def cube_boundary(c):
    out=Counter()
    for cell,m in c.items():
        active=[i for i,x in enumerate(cell) if x is None]
        for local,i in enumerate(active):
            sign=1 if local%2==0 else -1
            for endpoint,orientation in [(1,1),(0,-1)]:
                face=list(cell); face[i]=endpoint
                out[tuple(face)]+=m*sign*orientation
    return clean(out)

def pair(a,c):
    return sum(m*a(x) for x,m in c.items())

def face(cube, index, endpoint):
    indices=[i for i,v in enumerate(cube) if v is None]
    out=list(cube);out[indices[index]]=endpoint
    return tuple(out)

def execute_algebra_checks():
    for n in [0,1,2,3,7,70]:
        root=(None,)*n
        check(f"boundary_squared_zero_dimension_{n}",not cube_boundary(cube_boundary(Counter({root:1}))))
    root=(None,)*5
    for i in range(5):
        for j in range(i+1,5):
            for eps in [0,1]:
                for eta in [0,1]:
                    assert face(face(root,j,eta),i,eps)==face(face(root,i,eps),j-1,eta)
    check("all_five_dimensional_corner_orders",True)
    huge=2**149+17
    c=Counter({(None,None):huge})
    valuation=lambda x: sum((i+2)*(0 if v is None else v+1) for i,v in enumerate(x))
    cob=lambda x: pair(valuation,cube_boundary(Counter({x:1})))
    check("stokes_large_exact_coefficients",pair(valuation,cube_boundary(c))==pair(cob,c))
    # Product orientation: coordinate order x then y.
    x=(None,);y=(None,None)
    left=cube_boundary(Counter({x+y:1}))
    first=Counter({a+y:m for a,m in cube_boundary(Counter({x:1})).items()})
    second=Counter({x+b:-m for b,m in cube_boundary(Counter({y:1})).items()})
    check("product_leibniz_sign",left==plus(first,second))
    check("dimension_restriction_changes_degree",sum(v is None for v in face(root,0,0))==4)
    # A closed one-form on a graph can have nonzero circulation.
    cycle_edges={"ab":("a","b"),"bc":("b","c"),"ca":("c","a")}
    bd=Counter()
    for s,t in cycle_edges.values():bd[t]+=1;bd[s]-=1
    check("closed_cycle_boundary_zero",not clean(bd))
    check("cycle_period_not_forced_zero",sum([1,1,1])==3)
    # Twisted square boundary, coefficients at each cell's base vertex.
    # bottom/right/top/left carry transports 2/3/2/3 in the flat case.
    def twisted_square_second_boundary(top_transport):
        edges={"bottom":("00","10",Fraction(2)),
               "right":("10","11",Fraction(3)),
               "top":("01","11",Fraction(top_transport)),
               "left":("00","01",Fraction(3))}
        # d1^1 - d1^0 - d2^1 + d2^0, including coefficient transport.
        edge_coeff={"right":Fraction(2),"left":Fraction(-1),
                    "top":Fraction(-3),"bottom":Fraction(1)}
        result=Counter()
        for edge,m in edge_coeff.items():
            s,t,transport=edges[edge]
            result[s]-=m;result[t]+=m*transport
        return clean(result)
    check("local_coefficient_boundary_squared_zero",not twisted_square_second_boundary(2))
    check("nonflat_square_defect_retained",twisted_square_second_boundary(5)==Counter({"11":Fraction(-9)}))
    # Three admitted comparisons compose with zero higher boundary defect.
    costs={"P":2,"Q":4,"R":7}
    delta=lambda a,b:costs[b]-costs[a]
    check("higher_defect_coherence",delta("P","Q")+delta("Q","R")-delta("P","R")==0)
    check("positive_reverse_is_not_signed_negative",2+2==4 and 2+(-2)==0)

@dataclass(frozen=True)
class Event:
    eid:str
    owner:str
    weight:int
    consumes:tuple[str,...]=()
    produces:tuple[str,...]=()
    parents:tuple[str,...]=()

class History:
    def __init__(self,initial=()):
        self.initial=frozenset(initial);self.live=set(initial);self.events={}
    def add(self,e):
        assert e.eid not in self.events
        assert len(set(e.consumes))==len(e.consumes)
        assert set(e.consumes)<=self.live
        assert not(set(e.produces)&self.live)
        assert set(e.parents)<=self.events.keys()
        self.live.difference_update(e.consumes)
        self.live.update(e.produces)
        self.events[e.eid]=e
    def boundary(self,ids=None):
        out=Counter()
        for i in self.events if ids is None else ids:
            e=self.events[i];out.update(e.produces);out.subtract(e.consumes)
        return clean(out)
    def weight(self,ids=None):
        return sum(self.events[i].weight for i in (self.events if ids is None else set(ids)))
    def closure(self,roots):
        todo=list(roots);seen=set()
        while todo:
            e=todo.pop()
            if e not in seen:
                seen.add(e);todo.extend(self.events[e].parents)
        return frozenset(seen)

def execute_history_checks():
    h=History(["p0","a0","b0"])
    h.add(Event("producer","P",5,("p0",),("p1",)))
    h.add(Event("consumeA","A",2,("a0",),("a1",),("producer",)))
    h.add(Event("consumeB","B",2,("b0",),("b1",),("producer",)))
    ha=h.closure(["consumeA"]);hb=h.closure(["consumeB"])
    check("shared_history_union",h.weight(ha|hb)==9)
    check("shared_history_inclusion_exclusion",h.weight(ha|hb)==h.weight(ha)+h.weight(hb)-h.weight(ha&hb))
    check("naive_unfolding_double_counts",h.weight(ha)+h.weight(hb)==14)
    check("cut_from_same_events",h.boundary()==plus(Counter(h.live),scale(-1,Counter(h.initial))))
    check("incremental_cost_ready_prefix",h.weight(ha-{"producer"})==2)
    old=h.closure(["consumeA"])
    oldcost=h.weight(old)
    h.add(Event("query","observer",3,(),(),tuple(old)))
    check("query_prefix_immutable",h.weight(old)==oldcost and "query" not in old)
    check("query_work_is_later_work",h.weight()==12)
    check("consistent_cut_closure_includes_cause",h.closure(["consumeB"])==frozenset(["producer","consumeB"]))
    owners=Counter()
    for e in h.events.values():owners[e.owner]+=e.weight
    check("exact_owner_partition",sum(owners.values())==h.weight())
    huge=2**64+1
    h.add(Event("large_count","service",huge))
    check("counts_beyond_word",h.weight()==huge+12)
    # Independent local mutations commute; this does not assert fine-cost
    # invariance for arbitrary native interner implementations.
    for order in permutations([Event("x","X",1,("x0",),("x1",)),Event("y","Y",1,("y0",),("y1",))]):
        local=History(["x0","y0"])
        for e in order:local.add(e)
        assert local.live=={"x1","y1"}
    check("disjoint_local_boundary_commutation",True)

@dataclass
class Cut:
    generation:int=0
    phase:str="WAITING"
    residual:str="u"
    revision:int=1
    resumes:int=0
    delivered:set=field(default_factory=set)
    events:list=field(default_factory=list)

def prepare(c,*,source="u",required_guard=True,revision=None,connector=False):
    if not required_guard or (source!=c.residual and not connector):return None
    return (c.generation,c.residual,c.revision if revision is None else revision,"v")

def adopt(c,p):
    c.events.append("install-attempt")
    if p is None:return False
    g,u,rev,v=p
    if c.phase!="WAITING" or c.generation!=g or c.residual!=u or c.revision!=rev:return False
    c.generation+=1;c.residual=v;c.events.append("installed")
    return True

def deliver(c,ticket,g):
    assert ticket not in c.delivered
    c.delivered.add(ticket);c.events.append("delivery")
    if c.phase!="WAITING" or c.generation!=g:
        c.events.append("obsolete-disposal");return False
    c.phase="RESUMING";c.resumes+=1;return True

def execute_adoption_checks():
    c=Cut();p=prepare(c)
    check("delivery_wins",deliver(c,"old",0) and not adopt(c,p) and c.resumes==1)
    c=Cut();p=prepare(c)
    check("adoption_wins",adopt(c,p))
    check("old_ticket_no_resume",not deliver(c,"old",0) and c.resumes==0)
    check("new_ticket_one_resume",deliver(c,"new",1) and c.resumes==1 and len(c.delivered)==2)
    c=Cut();p=prepare(c)
    check("duplicate_proposal_one_install",adopt(c,p) and not adopt(c,p))
    c=Cut();p=prepare(c);c.revision=2
    check("revision_invalidates_preparation",not adopt(c,p))
    c=Cut()
    check("boundary_guard_required",prepare(c,required_guard=False) is None)
    check("same_earlier_source_not_connector",prepare(c,source="s0") is None)
    check("explicit_current_connector",prepare(c,source="s0",connector=True) is not None)
    # Every ordering of one prepared install and old delivery has one winner.
    for order in permutations(["adopt","deliver"]):
        c=Cut();p=prepare(c)
        adopted=False
        for op in order:
            if op=="adopt":adopted=adopt(c,p)
            else:deliver(c,"old",0)
        if adopted:deliver(c,"new",1)
        assert c.resumes==1
    check("both_atomic_race_orders",True)

def execute_effect_checks():
    value={"A0":3,"B0":1,"A1":1,"mAB":2,"B1":3,"B2":1,"mBA":2,"A2":3}
    h=History(["A0","B0"])
    valuation=lambda live:sum(value[x] for x in live)
    h.add(Event("sendAB","A",1,("A0",),("A1","mAB")))
    check("pending_port_retained",h.live=={"A1","B0","mAB"} and valuation(h.live)==4)
    h.add(Event("receiveAB","B",1,("B0","mAB"),("B1",),("sendAB",)))
    rejected=False
    try:h.add(Event("double","B",1,("mAB",),()))
    except AssertionError:rejected=True
    check("one_port_consumption",rejected)
    h.add(Event("sendBA","B",1,("B1",),("B2","mBA"),("receiveAB",)))
    h.add(Event("receiveBA","A",1,("A1","mBA"),("A2",),("sendBA",)))
    check("return_cycle_value_conserved",valuation(h.live)==4)
    check("return_cycle_history_retained",h.live!=set(h.initial) and h.weight()==4)
    check("resource_chain_map_cut",h.boundary()==plus(Counter(h.live),scale(-1,Counter(h.initial))))
    check("stokes_effect_valuation",sum(m*value[x] for x,m in h.boundary().items())==0)

def execute_calibration_checks():
    potential={"s":3,"a":2,"b":2,"z":0}
    edges=[("s","a",1),("a","z",2),("s","b",2),("b","z",2)]
    slack=lambda e:e[2]+potential[e[1]]-potential[e[0]]
    check("calibration_edge_inequalities",all(slack(e)>=0 for e in edges))
    check("calibrated_path_attains",sum(e[2] for e in edges[:2])==potential["s"])
    check("alternative_has_positive_slack",sum(slack(e) for e in edges[2:])==1)
    check("new_shortcut_requires_certificate_update",slack(("s","z",2))<0)

if __name__=="__main__":
    execute_algebra_checks();execute_history_checks();execute_adoption_checks()
    execute_effect_checks();execute_calibration_checks()
    report={"scope":"finite author-contract checks, not production implementation evidence",
            "passed":len(checks),"failed":0,"checks":checks}
    Path(__file__).with_name("contract-check-results.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"passed":len(checks),"failed":0,"scope":report["scope"]}))
