require import AllCore List Distr.

type value, commitment, openingkey, message, advice.
type snm_relation = message -> message -> bool.


require import Commitment.
clone import CommitmentProtocol as CP with type value      <- value,
                                           type message    <- message,
                                           type commitment <- commitment,
                                           type openingkey <- openingkey.


op rndstr : (bool list) distr. (* randomness *)
op Com (x : value) (r : bool list) (m : message) : commitment * openingkey.
op Ver : value -> message * (commitment * openingkey) -> bool.
op Dpk : value distr.

(* the key generation is efficient *)
axiom Dpk_ll : is_lossless Dpk. 
(* the randomness sampling is efficient *)
axiom rndstr_ll : is_lossless rndstr. 
(* the commitment scheme is sound (i.e., functional) *)
axiom S_correct pk r : pk \in Dpk => forall m, Ver pk (m, (Com pk r m)). 


module type AdvSNM = {
  proc init(pk : value, h : advice) : (message distr) * snm_relation
  proc commit(c : commitment, r : snm_relation) : commitment
  proc decommit(d : openingkey) : openingkey * message
}.


module type Simulator = {
  proc simulate(pk : value, r : snm_relation, dd : message distr) : message *  commitment * openingkey
}.


module SG0(A : AdvSNM) = {
  proc main(h : advice) : bool = {
    var m,m',c,c',d,d',pk, rs, md, rel;
    pk                 <$ Dpk;
    (md, rel)          <- A.init(pk,h);
    m                  <$ md;
    rs                 <$ rndstr;
    (c, d)             <- Com pk rs m;
    c'                 <- A.commit(c, rel);
    (d', m')           <- A.decommit(d); 
      return Ver pk (m', (c', d'))
             /\ rel m m' /\ (c,d) <> (c',d');
  }
}.


module SG1(A : AdvSNM, S : Simulator) = {
  proc main(h : advice) : bool = {
    var pk, m, c', d', m', md, mrel;    
    pk                 <$ Dpk; 
    (md, mrel)         <- A.init(pk,h);
    m                  <$ md;
    (m', c',  d')      <- S.simulate(pk, mrel, md);
    return mrel m m';
  }
}.

(*  

A commitment scheme C is (simulation-based) non-malleable iff for any
adversary A there exists a simulator S so that for any advice string h
the advantage AdvS(C, A, S, h) is negligible, where AdvS(C, A, S, h)
:= Pr [r ← SG0(C, A).main(h) : r = 1] − Pr [r ← SG1(C, A, S).main(h) :
r = 1] .

*)



(* Simulation-Based Non-Malleability for (Possibly) Stateful Commitment Scheme *)
                                           
module SEG0(CS:CommitmentScheme, A : AdvSNM) = {
  proc main(h : advice) : bool = {
    var pk, c,c',d,d',m,m',v, ssnmdistr, rel;    
    pk                 <- CS.gen(); 
    (ssnmdistr, rel)   <- A.init(pk,h);
    m                  <$ ssnmdistr;
    (c, d)             <- CS.commit(pk, m);
    c'                 <- A.commit(c, rel);
    (d', m')           <- A.decommit(d);    
    v                  <- CS.verify(pk, m', c', d');
    return v /\ rel m m' /\ (c,d) <> (c',d');
  }
}.


module SEG1(CS:CommitmentScheme, A : AdvSNM, S : Simulator) = {
  proc main(h : advice) : bool = {
    var m,m',pk,c,d, ssnmdistr, rel;    
    pk                 <- CS.gen(); 
    (ssnmdistr, rel)   <- A.init(pk, h);
    m                  <$ ssnmdistr;
    (m',c,d)           <- S.simulate(pk, rel, ssnmdistr);
    return rel m m';
  }
}.

