#!/usr/bin/env python3

from __future__ import annotations
from abc import ABC, abstractmethod
import itertools
import random

from pyparsing import Optional

from logic import *
from util import *
from proofrules import *
from parser import parse, fmla_parse, judgement_parse
from verifier import verify

# Use a verifier!! Gives you a list of sequents; unclosed obligations. Also gives you feedback. Use often in tactics.
#len(verify) == 0 is a good thing.


class Tactic(ABC):

    @abstractmethod
    def apply(self, seq: Sequent) -> set[Proof]:
        return set([seq])
    
class IdentityTactic(Tactic):

    def __init__(self,):
        pass

    def apply(self, seq: Sequent) -> set[Proof]:
        return set([(Proof(), seq, identityRule)])

class InstantiateForallTactic(Tactic):

    """
    A general tactic for proving sequents with a quantified
    formula in the context. The constructor takes a set of
    objects to instantiate the quantified variable with, and
    for each object `e`, `apply` returns a proof with one application
    of `@L` where the quantified variable is replaced with `e`
    in the context of the premise.
    """
    
    def __init__(self, grounds: set[Formula|Agent|Resource|Key]):
        self.grounds = grounds

    def apply(self, seq: Sequent) -> set[Proof]:
        pfs = set([])
        # seq is p1, ..., pn |- delta
        for p in seq.gamma:
            if not isinstance(p.p, Forall):
                continue
            # p is Proposition(@x . q)
            x = p.p.x
            q = p.p.p
            for e in self.grounds:
                # A new assumption to add to the context of the premise
                # by substituting e for x.
                new_assume = Proposition(apply_formula(q, {x: e}))
                # If this assumption is already in the context, don't bother
                # generating a proof
                if new_assume not in seq.gamma:
                    # The context for the premise of the proof that will be added
                    # contains the new assumption, and removes the @x . p judgement
                    # to avoid repeating the same step in the future.
                    new_gamma = [r for r in seq.gamma if r != p] + [new_assume]
                    # Before adding the proof, need to check whether delta is a
                    # truth (proposition) judgement or affirmation.
                    # This determines whether to use the "normal" @L rule, or the
                    # version that matches affirmation judgements.
                    which_rule = forallLeftRule if isinstance(seq.delta, Proposition) else forallLeftAffRule
                    # Add the proof to the return set.
                    pfs |= set([Proof([Sequent(new_gamma, seq.delta)], seq, which_rule)])
        return pfs

class SignTactic(Tactic):

    """
    A tactic for incorporating a signed credential into
    assumptions as a `says` formula. The `says` formula
    obtained by applying the `Sign` rule to `cred` with
    the public key of `agent` is incorporated into the
    context of an application of `Cut`. So if this tactic
    were constructed as:
    
    SignTactic(parse('sign(open(#b, <r>), [k])'), Agent('#a'))
    
    And applied to the following sequent:
    
    iskey(#a, [k]), sign(open(#b, <r>), [k]) |- P

    Then it would yield the following proof.

                        T.0  T.1
    cut -------------------------------------------------
        iskey(#a, [k]), sign(open(#b, <r>), [k]) |- P

    The premise `T.0` will be a closed proof of
    `#a says open(#b, <r>)` if and only if:
        - The `cred` argument is in the context of the
          sequent that the tactic is applied to.
        - The sequent that the tactic is applied to
          has an `iskey` predicate that associates the
          `agent` argument with the key appearing in
          the `cred` argument, i.e. `iskey(#a, [k])` in
          this example.
    The premise `T.1` of the resulting proof will be a
    sequent (i.e., an open/unclosed premise) with a set
    of assumptions identical to those in the sequent that
    the tactic is applied to, but will also include
    `#a says open(#b, <r>)`. I.e.:

    #a says open(#b, <r>), iskey(#a, [k]), sign(open(#b, <r>), [k]) |- P

    If the two conditions listed above are not true of
    the sequent that the tactic is applied to, then
    `apply` returns the empty set.

    The proofs returned by this tactic can be closed by
    combining with other tactics using `ThenTactic`, or
    by applying other tactics to `pf.premises[1].conclusion`,
    (assuming `pf` is the returned proof), which will contain
    the unfinished sequent with the new `says` in its
    assumption, and chaining the two proofs together with
    `chain`.
    """
    
    def __init__(self, cred: Formula, agent: Agent):
        self._cred = cred
        self._ag = agent
        # _says is the formula that we want to introduce in the cut
        self._says = App(Operator.SAYS, 2, [agent, cred.args[0]])
        # _iskey associates agent to the key in cred
        self._iskey = App(Operator.ISKEY, 2, [agent, cred.args[1]])
        # cred and _iskey need to be present in the sequent to
        # apply this tactic
        self._reqs = [
            Proposition(cred),
            Proposition(self._iskey)
        ]

    def apply(self, seq: Sequent) -> set[Proof]:
        # make sure all of the required assumptions are present
        if not all(p in seq.gamma for p in self._reqs):
            return set([])
        # if the `says` formula is already in the sequent's
        # assumptions, then there is no need to introduce it
        # again
        if Proposition(self._says) in seq.gamma:
            return set([])
        # cutgoal is the formula that we want to prove in the
        # left premise of the `cut` appliction
        cutgoal = Sequent(seq.gamma, Proposition(self._says))
        # `Sign` requires proving `_iskey` and `_cred`
        # We already checked that these are in the context,
        # so if we've gotten this far then we know that both
        # are proved with one application of the identity rule
        pf_iskey = get_one_proof(Sequent(seq.gamma, Proposition(self._iskey)), RuleTactic(identityRule))
        pf_cred = get_one_proof(Sequent(seq.gamma, Proposition(self._cred)), RuleTactic(identityRule))
        # The left premise of the cut is proved by combining these proofs
        # using the `Sign` rule
        pf_cutgoal = Proof([pf_iskey, pf_cred], cutgoal, signRule)
        # The right premise of the cut will copy the assumptions
        # in the current sequent, and add _says
        new_gamma = (
            seq.gamma + 
            [Proposition(self._says)]
        )
        newgoal = Sequent(new_gamma, seq.delta)
        # We need to look at the delta (proof goal) of the given sequent
        # to determine whether to use the version of `cut` for truth
        # or affirmation judgements
        whichRule = cutRule if isinstance(seq.delta, Proposition) else affCutRule
        # Now put everything together and return the proof
        return set([Proof([pf_cutgoal, newgoal], seq, whichRule)])

class CertTactic(Tactic):

    """
    A tactic for incorporating a signed credential into

    """
    
    def __init__(self, agent: Agent, k: Key, ca: Agent, caK: Key):
        #args = 
        
        self._ag = agent
        # _says is the formula that we want to introduce in the cut
        self._iskey = App(Operator.ISKEY, 2, [agent, k])
        # _iskey associates agent to the key in cred
        self._ca = App(Operator.ISCA, 1, [ca])

        self._cert = App(Operator.SAYS, 2, [ca, self._iskey])
        # cred and _iskey need to be present in the sequent to
        # apply this tactic
        self._reqs = [
            Proposition(self._cert),
            Proposition(self._ca)
        ]

    def apply(self, seq: Sequent) -> set[Proof]:
        # make sure all of the required assumptions are present
        if not all(p in seq.gamma for p in self._reqs):
            return set([])
        # if the `says` formula is already in the sequent's
        # assumptions, then there is no need to introduce it
        # again
        if Proposition(self._iskey) in seq.gamma:
            return set([])
        # cutgoal is the formula that we want to prove in the
        # left premise of the `cut` appliction
        cutgoal = Sequent(seq.gamma, Proposition(self._iskey))
        # `Sign` requires proving `_iskey` and `_cred`
        # We already checked that these are in the context,
        # so if we've gotten this far then we know that both
        # are proved with one application of the identity rule
        pf_ca = get_one_proof(Sequent(seq.gamma, Proposition(self._ca)), RuleTactic(identityRule))
        pf_cert = get_one_proof(Sequent(seq.gamma, Proposition(self._cert)), RuleTactic(identityRule))
        # The left premise of the cut is proved by combining these proofs
        # using the `Cert` rule
        pf_cutgoal = Proof([pf_ca, pf_cert], cutgoal, certRule)
        # The right premise of the cut will copy the assumptions
        # in the current sequent, and add _says
        new_gamma = (
            seq.gamma + 
            [Proposition(self._iskey)]
        )
        newgoal = Sequent(new_gamma, seq.delta)
        # We need to look at the delta (proof goal) of the given sequent
        # to determine whether to use the version of `cut` for truth
        # or affirmation judgements
        whichRule = cutRule if isinstance(seq.delta, Proposition) else affCutRule
        # Now put everything together and return the proof
        return set([Proof([pf_cutgoal, newgoal], seq, whichRule)])


class RuleTactic(Tactic):

    """
    A general tactic for applying the rules in `proofrules` to make
    single-step progress on a proof. This does not attempt to apply
    the quantifier rules, and will raise `ValueError` if the constructor
    is given such a rule.
    """
    
    def __init__(self, rule: Rule):
        match rule:
            case Rule(_, _, '@L')|Rule(_,_,'@R'):
                raise ValueError(f'RuleTactic cannot be applied to @L or @R')
        self._rule = rule

    def apply(self, seq: Sequent) -> set[Proof]:
        pfs = set([])
        # Attempt to unify the given sequent with the conclusion of the rule.
        rhos = list(matchs_sequent(self._rule.conclusion, seq, {}))
        # There may be more than one substitution that unifies the
        # sequent with the rule, i.e., more than one opportunity to
        # apply the rule to this sequent. This tactic will generate
        # proofs for all of them.
        for rho in rhos:
            # We want to remove any assumptions from the sequent that
            # were used to match the rule. This is a general heuristic
            # to avoid infinite applications of the same step when
            # the tactic is combined with repetitive tactics.
            rule_gamma = apply_sequent(self._rule.conclusion, rho).gamma
            red_gamma = [p for p in seq.gamma if p not in rule_gamma]
            # The premises of each proof are obtained by applying
            # the substitution rho to each rule premise, and adding
            # the assumptions from the goal sequent that were not
            # used to match with the rule.
            prems = [
                Sequent(
                    list(set(apply_sequent(prem, rho).gamma + red_gamma)), 
                    apply_sequent(prem, rho).delta
                ) 
                for prem in self._rule.premises
            ]
            # Add the proof to the return set, and carry on
            pfs |= set([Proof(prems, seq, self._rule)])
        return pfs

class ThenTactic(Tactic):

    """
    A combinator tactic to apply a sequence of tactics,
    chaining the proofs obtained by later tactics to any
    unclosed branches of proofs generated by earlier tactics.

    This can be used in two modes, depending on the value 
    of `pass_on` given to the constructor. If `pass_on` is 
    `True`, then if the first tactic in the sequence fails
    to produce any proofs, then the next tactic is applied
    to the original sequent. If `pass_on` is `False`, then
    when the first tactic produces no proofs, no further
    tactics are applied.

    Most applications of this tactic will want to use it with
    `pass_on` set to `True`, so this is the default value.
    """
    
    def __init__(self, ts: list[Tactic], pass_on=True):
        self._ts = ts
        self._pass = pass_on

    def apply(self, seq: Sequent) -> set[Proof]:
        pfs = set([])
        # This tactic calls itself recursively, and
        # will terminate when the sequence of tactics
        # to apply is empty.
        if len(self._ts) > 0:
            # The first tactic in the sequence is applied directly,
            # and the remaining are dealt with recursively.
            t1, t2 = self._ts[0], ThenTactic(self._ts[1:], pass_on=self._pass)
            t1_pfs = t1.apply(seq)
            # If the first tactic didn't yield any proofs, then
            # return an empty set if `pass_on` is `False`.
            # Otherwise, just proceed to the next tactic
            # with the original sequent.
            if len(t1_pfs) == 0:
                return t2.apply(seq) if self._pass else set([])
            else:
                for pf1 in t1_pfs:
                    # For each proof returned by the first tactic,
                    # find the set of remaining unclosed branches
                    # (i.e. "obligations") by calling verify.
                    obs = [ob for ob in verify(pf1) if ob != seq]
                    # If all of the branches are closed, then
                    # simply return this proof.
                    # No future tactics will be able to make further
                    # progress on it.
                    if len(obs) == 0:
                        return set([pf1])
                    # Generate proofs for the remaining obligations
                    # by applying the rest of the tactic sequence
                    # to them
                    t2_pfs = [(ob, t2.apply(ob)) for ob in obs]
                    # Now we have a *set* of proofs for each unclosed
                    # branch. We don't know a priori which of them
                    # will be able to close, so we return proofs that
                    # try every combination of proof for all premises.
                    combs = list(
                        itertools.product(
                            *[pf if len(pf) > 0 else [ob] for ob, pf in t2_pfs]
                        )
                    )
                    # The list of combinations can be empty if there were
                    # no proofs for one of the obligations.
                    if len(combs) > 0:
                        for comb in combs:
                            # If this isn't the case, then chain each combination
                            # of obligation proofs onto the current proof,
                            # and add it to the return set.
                            chains = {ob: comb[i] for i, ob in enumerate(obs)}
                            pfs |= set([chain(pf1, chains)])
                    else:
                        # If this happens, then just add the current proof.
                        pfs |= set([pf1])
        return pfs

class WeirdTactic() :
    def __init__(self, a: Agent, r: Resource,  b : Agent):
        self._a = a
        self._b = b
        self._r = r
    
    def apply(self, seq : Sequent) -> set[Proof]:
        pfs = set([])
        for prop in seq.gamma:
            if not isinstance(prop.p, Forall):
                continue
            # prop is Proposition(@x . q)
            # prop.p is Forall(x, q)
            # prop.p.p is q, ANOTHER FORMULA (not a proposition)
            x = prop.p.x
            q = prop.p.p
            #new_assume1 = Proposition(apply_formula(q, {x: self._a}))
            newq = apply_formula(q, {x: self._a})
            new_assume1 = Proposition(newq)
            new_gamma1 = [r for r in seq.gamma if r != prop] + [new_assume1]
            
            if not isinstance(newq, Forall):
                #print('error')
                continue
            y = newq.x
            q2 = newq.p
            newq2 = apply_formula(q2, {y: self._r})
            new_assume2 = Proposition(newq2)
            new_gamma2 = [r for r in seq.gamma if r != prop] + [new_assume2]

            if not isinstance(newq2, App):
                continue
                #print('error2')
            if not newq2.arity == 2:
                print('error3')
                continue
            #if not q2.op == logic.IMPLIES:
            #    print('error')
            q3 = newq2.args[1]
            qunused = newq2.args[0]


            #For the branch that checks qunused
            branch_delta = Proposition(qunused)
            branch_gamma = [r for r in seq.gamma if r != prop]

            #For main line
            main_delta = seq.delta
            main_gamma = [r for r in seq.gamma if r != prop] + [Proposition(q3)]


            if not isinstance(q3, Forall):
                continue
                print('error4')
            z = q3.x
            q4 = q3.p
            finalform = apply_formula(q4, {z: self._b})
            new_assume3 = Proposition(finalform)

            new_gamma3 = [r for r in seq.gamma if r != prop] + [new_assume3]
            ###if new_assume not in seq.gamma:
                    # The context for the premise of the proof that will be added
                    # contains the new assumption, and removes the @x . p judgement
                    # to avoid repeating the same step in the future.
                #new_gamma = [r for r in seq.gamma if r != p] + [new_assume]
                    # Before adding the proof, need to check whether delta is a
                    # truth (proposition) judgement or affirmation.
                    # This determines whether to use the "normal" @L rule, or the
                    # version that matches affirmation judgements.
                #which_rule = forallLeftRule if isinstance(seq.delta, Proposition) else forallLeftAffRule
                    # Add the proof to the return set.
            newseq1 = Sequent(new_gamma1, seq.delta)
            newseq2 = Sequent(new_gamma2, seq.delta)
            newseq3 = Sequent(new_gamma3, seq.delta)
            pf1 = Proof([newseq1], seq, forallLeftRule)
            pf2 = Proof([newseq2], newseq1, forallLeftRule)
            

            branchseq = Sequent(branch_gamma, branch_delta)
            mainseq = Sequent(main_gamma, main_delta)
            
            pf3 = Proof([branchseq, mainseq], newseq2, impLeftAffRule)
            
            pf4 = Proof([newseq3], mainseq, forallLeftRule)

            realpf2 = chain(pf1, {newseq1: pf2})
            realpf3 = chain(realpf2, {newseq2: pf3})
            realpf4 = chain(realpf3, {mainseq: pf4})
            #print(proof_stringify(realpf4))
            pfs |= set([realpf4])
            
        #for pf in pfs:
        #    print(proof_stringify(pf))
        return pfs
    

class OrElseTactic(Tactic):

    """
    Apply a sequence of tactics until progress is made.
    Specifically, continue applying tactics in the
    given sequence while they fail to produce any proofs.
    When a tactic does produce proofs, return them and
    stop applying further tactics.
    """
    
    def __init__(self, ts: list[Tactic]):
        self._ts = ts

    def apply(self, seq: Sequent) -> set[Proof]:
        # This works in a similar way to ThenTactic,
        # making recursive calls to itself
        # for as long as tactics attempted so far do not
        # produce any proofs.
        if len(self._ts) > 0:
            t_pfs = self._ts[0].apply(seq)
            if len(t_pfs) == 0:
                return OrElseTactic(self._ts[1:]).apply(seq)
            else:
                return t_pfs
        return set([])

def chain(pf: Proof, chains: dict[Sequent, Proof]) -> Proof:
    """
    Chain proofs for unclosed branches of a proof into
    the original proof. An unclosed branch in a proof
    will manifest as a `Sequent` object in a premise,
    rather than a `Proof` object. The `chains` argument
    maps these sequents to proofs, which are substituted
    into the given proof `pf`.
    
    Args:
        pf (Proof): A proof, potentially containing unclosed
            branches.
        chains (dict[Sequent, Proof]): Mapping of unfinished
            branches to their proofs.
    
    Returns:
        Proof: The proof described in the summary.
    """
    # If the mapping contains a proof for the original
    # conclusion, then return it.
    if pf.conclusion in chains:
        return chains[pf.conclusion]
    new_prems = []
    # Look for unfinished branches among the premises.
    for prem in pf.premises:
        if isinstance(prem, Proof):
            # If a premise already has a proof, it may still
            # contain unfinished branches. Recurse on it.
            new_prems.append(chain(prem, chains))    
        elif prem in chains:
            # Otherwise, if the premise is a sequent mapped to
            # a proof by the given `chains`, then use the mapping
            new_prems.append(chains[prem] if chains[prem] is not None else prem)
        else:
            # Otherwise, it is a sequent that the mapping does
            # not have a proof for. Leave it unchanged.
            new_prems.append(prem)
    return Proof(new_prems, pf.conclusion, pf.rule)

def get_one_proof(seq: Sequent, t: Tactic) -> Optional[Proof]:
    """
    Convenience function to look for a closed proof
    in the set returned by a tactic.
    
    Args:
        seq (Sequent): A sequent to apply the tactic to.
        t (Tactic): Tactic to apply.
    
    Returns:
        Optional[Proof]: If the tactic yields a closed proof,
            i.e., one for which `verify` returns an empty set
            of obligations, then that proof is returned.
            Otherwise, `None`.
    """
    for pf in t.apply(seq):
        if len(verify(pf)) == 0:
            return pf
        #print(proof_stringify(pf))
        #print('DISTINCT PROOF')
        #for a in verify(pf):
        #    print(sequent_stringify(a))
            #print('/n')
    return None

def prove2(seq: Sequent) -> Optional[Proof]:
    t = ThenTactic([
        SignTactic(parse('sign(iskey(#root, [ca:63:85:95:dc:f9:48:e4:cd:46:ec:4d:93:08:c5:c0]), [45:fb:a2:de:b4:da:6b:62:30:4f:be:ce:1c:05:52:e7])'), Agent('#newuser')),
        CertTactic(Agent('#root'), Key('[ca:63:85:95:dc:f9:48:e4:cd:46:ec:4d:93:08:c5:c0]'), Agent('#newuser'), Key('[45:fb:a2:de:b4:da:6b:62:30:4f:be:ce:1c:05:52:e7]')),
        SignTactic(parse('sign((open(#calebkoo, <bigsecret.txt>)), [ca:63:85:95:dc:f9:48:e4:cd:46:ec:4d:93:08:c5:c0])'), Agent('#root')),
        RuleTactic(identityRule)
    ])
    
    #print(proof_stringify(get_one_proof(seq, t)))
    return get_one_proof(seq, t)

def prove(seq: Sequent) -> Optional[Proof]:
    """
    Produce a proof for a given sequent, if the
    student's tactic is able to find one. You
    should implement this function by developing
    one or more tactics for the authorization
    policies specified in the lab, and applying them
    to `seq`.
    
    Args:
        seq (Sequent): Sequent to prove.
    
    Returns:
        Optional[Proof]: A closed proof of `seq`, if
            one exists. Otherwise `None`.
    """
    #FIRST ONE
    q1 = judgement_parse('#root says open(#calebkoo, <calebkoo.txt>)')
    q2 = judgement_parse('#root says open(#calebkoo, <shared.txt>)')
    q3 = judgement_parse('#root says open(#calebkoo, <secret.txt>)')
    if q1 == seq.delta:  
        t = ThenTactic([
            SignTactic(parse('sign(iskey(#root, [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
            CertTactic(Agent('#root'), Key('[2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
            SignTactic(parse('sign((open(#calebkoo, <calebkoo.txt>)), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])'), Agent('#root')),
            RuleTactic(identityRule)
        ])
    
    #print(proof_stringify(get_one_proof(seq, t)))
    
     
    # NEXT ONE
    #t= ThenTactic([
    #SignTactic(parse('sign(iskey(#root, [2b:8f:e8:9b]), [43:c9:43:e6])'), Agent('#ca')),
    #CertTactic(Agent('#root'), Key('[2b:8f:e8:9b]'), Agent('#ca'), Key('[43:c9:43:e6]')),
    ##SignTactic(parse('sign(((@A . (((#mfredrik says open(A, <shared.txt>)) -> open(A, <shared.txt>))))), 
    # [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]), Agent('#root')),
    #RuleTactic(forallLeftRule),
    #RuleRactic(saysLeftRule),
# This succesfully gets you to mfred says open(e, shared) -> open(e, shared) |- root aff open(koo, <shared>)
    # CertTactic(Agent('#mfrederik'), Key('[d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
# Gives you mfrederik key right
    # SignTactic(parse('sign((open(#calebkoo, <shared.txt>)), [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47])'), Agent('#mfrederik')),
# Gives mfrederk says open(koo, shared.txt)
    # RuleTactic(impLeftAffRule),
#Deals with the if, should yield open(calebkoo, <shared.txt>). Deal with other thing? Matching e to calebkoo?
    # RuleTactic(SaysLeftRule)
#root says open(koo, shared) |- root aff open(koo, shared) 
    # RuleTactic(SaysRightRule)
#root says open(koo, shared)  |- root says open(koo, shared) 
    #RuleTactic(identityRule)
    #])
    if q2 == seq.delta: 
        t= ThenTactic([
            SignTactic(parse('sign(iskey(#root, [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
            SignTactic(parse('sign(iskey(#mfredrik, [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47]), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
            CertTactic(Agent('#root'), Key('[2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
            SignTactic(parse('sign(((@A . (((#mfredrik says open(A, <shared.txt>)) -> open(A, <shared.txt>))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])'), Agent('#root')),
            CertTactic(Agent('#root'), Key('[2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
            CertTactic(Agent('#mfredrik'), Key('[d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
            SignTactic(parse('sign((open(#calebkoo, <shared.txt>)), [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47])'), Agent('#mfredrik')),
            #this gives "root says "@a mfredrik says...
            RuleTactic(saysRightRule),
            RuleTactic(saysLeftRule),
            InstantiateForallTactic(set([Agent('#calebkoo')])),
            
            
            RuleTactic(impLeftAffRule),
            RuleTactic(identityRule),
            #up to here is fine. However, we're not getting "mfredrik says open(calekoo, shared.txt)" for some reason.
            RuleTactic(affRule),
            RuleTactic(identityRule),
        ])
    #DON't MISS THIS: TO CHANGE A 'sign' to a 'says,' you must FIRST sign iskey as CA; then, certTactic that signing for the CA; THEN signtactic the
    # statement itself.

    #LAST ONE
    if q3 == seq.delta:
        t = ThenTactic([
            # start by adding everything we want
            SignTactic(parse('sign(iskey(#root, [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
            SignTactic(parse('sign(iskey(#mfredrik, [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47]), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
            SignTactic(parse('sign(iskey(#dsduena, [db:b2:b9:b7:01:83:9c:3e:7d:ac:c4:87:00:cd:79:2f]), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
            SignTactic(parse('sign(iskey(#justinyo, [d2:15:e7:01:be:ef:fa:e6:08:ca:6c:bd:90:f4:1b:af]), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
            SignTactic(parse('sign(iskey(#mdhamank, [71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f]), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),

            CertTactic(Agent('#root'), Key('[2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
            CertTactic(Agent('#mfredrik'), Key('[d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
            CertTactic(Agent('#dsduena'), Key('[db:b2:b9:b7:01:83:9c:3e:7d:ac:c4:87:00:cd:79:2f]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
            CertTactic(Agent('#justinyo'), Key('[d2:15:e7:01:be:ef:fa:e6:08:ca:6c:bd:90:f4:1b:af]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
            CertTactic(Agent('#mdhamank'), Key('[71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),

            SignTactic(parse('sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])'), Agent('#root')),
            
            SignTactic(parse('sign((open(#mfredrik, <secret.txt>)), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])'), Agent('#root')),
            SignTactic(parse('sign((open(#dsduena, <secret.txt>)), [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47])'), Agent('#mfredrik')),
            SignTactic(parse('sign((open(#justinyo, <secret.txt>)), [db:b2:b9:b7:01:83:9c:3e:7d:ac:c4:87:00:cd:79:2f])'), Agent('#dsduena')),
            SignTactic(parse('sign((open(#mdhamank, <secret.txt>)), [d2:15:e7:01:be:ef:fa:e6:08:ca:6c:bd:90:f4:1b:af])'), Agent('#justinyo')),
            SignTactic(parse('sign((open(#calebkoo, <secret.txt>)), [71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f])'), Agent('#mdhamank')),

            # affrule
            #changes |- root aff calebkoo can open
            RuleTactic(saysRightRule),
            #leftsaysrule
            #mfred can open...
            RuleTactic(saysLeftRule),
            RuleTactic(saysLeftRule),
            

            #We now should have everything we need.
            WeirdTactic(Agent('#mfredrik'), Resource('<secret.txt>'), Agent('#dsduena')),
            #currently, we have (mfred says dsduena can open) + (mfred can open) + (root says for if mfred can open -> if mfred says ds can open -> ds can open)
            # |- root aff calebkoo can open

            #leftsaysrule again
            #if mfred...
            RuleTactic(saysLeftRule),

            #leftimpaff
            #2 things to confirm. One is |- mfred can open, which is just by identity.
            #(mfred says dsduena can open) + if mfred says ds can open, ds can open (true) |- root aff calebkoo can open
            RuleTactic(impLeftAffRule),
            RuleTactic(identityRule),
            #leftimpaff again
            #2 things to confirm. One is |- mfred says dsduena can open, which is just by identity.
            #ds can open |- root aff calebkoo can open.
            RuleTactic(impLeftAffRule),
            RuleTactic(identityRule),

            #We legit just repeat "latest weirdtactic" + leftsaysrule + 2xleftimpaff until cows come home.
            SignTactic(parse('sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])'), Agent('#root')),
            RuleTactic(saysLeftRule),
            WeirdTactic(Agent('#dsduena'), Resource('<secret.txt>'), Agent('#justinyo')),
            RuleTactic(saysLeftRule),
            RuleTactic(saysLeftRule),
            RuleTactic(impLeftAffRule),
            RuleTactic(identityRule),
            RuleTactic(impLeftAffRule),
            RuleTactic(identityRule),

            SignTactic(parse('sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])'), Agent('#root')),
            RuleTactic(saysLeftRule),
            WeirdTactic(Agent('#justinyo'), Resource('<secret.txt>'), Agent('#mdhamank')),
            RuleTactic(saysLeftRule),
            RuleTactic(impLeftAffRule),
            RuleTactic(identityRule),
            RuleTactic(impLeftAffRule),
            RuleTactic(identityRule),

            SignTactic(parse('sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])'), Agent('#root')),
            RuleTactic(saysLeftRule),
            WeirdTactic(Agent('#mdhamank'), Resource('<secret.txt>'), Agent('#calebkoo')),
            RuleTactic(saysLeftRule),
            RuleTactic(impLeftAffRule),
            RuleTactic(identityRule),
            RuleTactic(impLeftAffRule),
            RuleTactic(identityRule),

            #Should yield ckoo can open |- root aff ckoo can open
            RuleTactic(affRule),
            RuleTactic(identityRule),
        ])
    
    #print(proof_stringify(get_one_proof(seq, t)))
    #t.apply(seq)
    return get_one_proof(seq, t)

if __name__ == '__main__':

    #in class live coding
    #seq = parse('@x, #A says iskey(x, [pk]) |- P')
    #for pf in tn.apply(seq):
    #    print(stringify())
    seq = parse('P, Q |- P')
    for pf in IdentityTactic().apply(seq):
        print(stringify(pf))

    s#eq = parse('iskey(#a, [pka]), sign(P, [pka]) |- #a says P')
    #t = SignTactic(parse('sign(P, [pka])'), Agent('#a'))
    #for pf in t.apply(seq):
    #    print(stringify(pf))

    pass
