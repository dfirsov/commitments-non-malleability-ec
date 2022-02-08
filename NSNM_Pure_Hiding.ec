pragma Goals:printall.
require import DBool List Real.
require import Commitment.
require import Distr AllCore.

require import D1D2.
require WholeMsg.

require import NSNM_Definition.
require CommitmentUnpredictability.

theory SNM_binding_theory.


clone import CommitmentProtocol as CP with type value      <- value,
                                           type message    <- message,
                                           type commitment <- commitment,
                                           type openingkey <- openingkey.



clone import CommitmentUnpredictability as CU with type value      <- value,
                                           type message    <- message,
                                           type commitment <- commitment,
                                           type openingkey <- openingkey,
                                           op Dpk <- Dpk,
                                           op Ver <- Ver,
                                           op Com <- Com,
                                           op rndstr <- rndstr.


clone import D1D2 with type message <- message.

clone import WholeMsg with type ain <- advice,
                           type message <- bool,
                           op m1 <- false,
                           op m2 <- true.



module HidingExperiment0 (U:Unhider) = {
  proc main() : bool = {
    var c, d,b',x,r,m1,m2;
    x        <$ Dpk;
    (m1, m2) <@ U.choose(x);
    r <$ rndstr;
    (c, d)   <- Com x r m1;
    b'       <@ U.guess(c);
    return b';
  }
}.


module HidingExperiment1 (U:Unhider) = {
  proc main() : bool = {
    var c, d,b',x,r,m1,m2;
    x        <$ Dpk;
    (m1, m2) <@ U.choose(x);
    r <$ rndstr;
    (c, d)   <- Com x r m2;
    b'       <@ U.guess(c);
    return b';
  }
}.


section.

module HEP = {
    var m1, m2 : message
}.


module HEPT0 (U:Unhider) = {
  var b' : bool
  var x : value
  var r : bool list
  proc main() : bool = {
    var c, d;
    x        <$ Dpk;
    (HEP.m1, HEP.m2) <@ U.choose(x);
    r <$ rndstr;
    (c, d)   <- Com x r HEP.m1;
    b'       <@ U.guess(c);
    return b';
  }
}.


module HEPT1 (U:Unhider) = {
  var b' : bool
  var x : value
  var r : bool list
  proc main() : bool = {
    var c, d;
    x        <$ Dpk;
    (HEP.m1, HEP.m2) <@ U.choose(x);
    r <$ rndstr;
    (c, d)   <- Com x r HEP.m2;
    b'       <@ U.guess(c);
    return b';
  }
}.


module H(U : Unhider) = {
  var m1, m2 : message
  var pk : value
  var c,c' : commitment
  var b' : bool
  var d,d' : openingkey
  var rdif : bool

  proc init(y : value, h:advice) = {
    pk <- y;
    (m1, m2) <@ U.choose(pk);
    return (duniform [m1;m2], fun (m1 m2 : message) => m1 = m2);
  }

  proc commit(z : commitment, r : snm_relation) : commitment  = {
    var rs;
    b' <- U.guess(z);
    rs <$ rndstr;
    (c',d') <- Com pk rs (if b' then m2 else m1); 
    return c';
  }

  proc decommit(o : openingkey) : openingkey * message = {
      return  (if b' then (d',m2) else (d',m1));
  }  
  
}.


declare module A : Unhider {H, HEPT0, HEPT1, HEP}.



local module SNM_G0'(A : AdvSNM) = {
  var m : message

  proc main(h : advice) : bool = {
    var pk, c, d, c', d', m', rs, md, rel;
    pk                 <$ Dpk;
    (md, rel)                 <- A.init(pk, h);
    m                  <$ md;
    rs                 <$ rndstr;
    (c, d)             <- Com pk rs m;
    c'                 <- A.commit(c, rel);
    (d', m')           <- A.decommit(d); 
      return Ver pk (m', (c', d'))
             /\ rel m m' /\ (c,d) <> (c',d');
  }
}.


local module SNM_G1'(A : AdvSNM, S : Simulator) = {
  proc main(h : advice) : bool = {
    var pk, m, c', d', m', md, rel;    
    pk                 <$ Dpk; 
    (md, rel)                 <- A.init(pk, h);
    m                  <$ md;
    (m', c',  d')      <- S.simulate(pk, rel);
    return rel m m';
  }
}.


axiom Ag_ll : islossless A.guess.
axiom Ac_ll : islossless A.choose.


(* the hiding-adversary who returns two equal messages can be turned into
adversary who never returns equal messages and whose hiding-advantage is greater 
or equal than the advantage of the first one *)
axiom qq1 &m : Pr[ HEPT0(A).main() @ &m : HEP.m1 <> HEP.m2 ] = 1%r.
axiom qq2 &m : Pr[ HEPT1(A).main() @ &m : HEP.m1 <> HEP.m2 ] = 1%r.
axiom qq0 : phoare [ A.choose : true ==> res.`1 <> res.`2 ] = 1%r.


lemma qq0h : 
  hoare [ A.choose : true ==> res.`1 <> res.`2 ].
proof.  conseq qq0.
qed.


local lemma game1 &m h : forall (S <: Simulator),
   Pr[ SNM_G1'(H(A), S).main(h) @ &m : res ] <= 1%r/2%r.
proof. move => S. byphoare (_: arg = h ==> _) =>//.
proc. inline*.
swap 7 1. 
seq 6 : (md = duniform [H.m1; H.m2] /\ rel = (fun (m1 m2 : message) => m1 = m2) /\ H.m1 <> H.m2) (1%r/2%r).
wp. call (_: true). wp. rnd. skip. auto.
simplify. wp. 
conseq (_: true ==> H.m1 <> H.m2).
call (_:true ==> res.`1 <> res.`2). 
conseq qq0. 
wp. rnd.  skip. auto.
rnd. call (_:true). skip. progress.
rewrite duniform1E_uniq. smt. simplify. smt.
wp. hoare.
simplify.
call (_:true ==> res.`1 <> res.`2). apply qq0h.
wp. rnd.  skip. auto. auto.
qed.



local lemma qq1_impl &m : Pr[ HEPT0(A).main() @ &m : HEP.m1 = HEP.m2 ] = 0%r.
proof. 
have : Pr[ HEPT0(A).main() @ &m : true ] = 1%r.
byphoare =>//.
proc. inline*. call (_:true).
apply Ag_ll. wp. rnd. call Ac_ll. rnd. skip.  smt.
rewrite Pr[mu_split HEP.m1 = HEP.m2] =>//.
rewrite - (qq1 &m). smt.
qed.


local lemma qq2_impl &m : Pr[ HEPT1(A).main() @ &m : HEP.m1 = HEP.m2 ] = 0%r.
proof. 
have : Pr[ HEPT1(A).main() @ &m : true ] = 1%r.
byphoare =>//.
proc. inline*. call (_:true).
apply Ag_ll. wp. rnd. call Ac_ll. rnd. skip.  smt.
rewrite Pr[mu_split HEP.m1 = HEP.m2] =>//.
rewrite - (qq1 &m). smt.
qed.


local module SNM_G0z(A : AdvSNM) = {
  var m : message
  proc main(h : advice) : bool = {
    var pk, c, d, c', d', m', rs, md, rel;
    pk                 <$ Dpk;
    (md, rel)                 <- A.init(pk, h);
    m                  <- D1.sample(H.m1,H.m2);
    rs                 <$ rndstr;
    (c, d)             <- Com pk rs m;
    c'                 <- A.commit(c, rel);
    (d', m')           <- A.decommit(d); 
      return Ver pk (m', (c', d'))
             /\ rel m m' /\ (c,d) <> (c',d');
  }
}.


local module SNM_G0y(A : AdvSNM) = {
  var m : message
  proc main(h : advice) : bool = {
    var pk, c, d, c', d', m', rs, md, rel;
    pk                 <$ Dpk;
    (md, rel)          <- A.init(pk,h);
    m                  <- D2.sample(H.m1,H.m2);
    rs                 <$ rndstr;
    (c, d)             <- Com pk rs m;
    c'                 <- A.commit(c, rel);
    (d', m')           <- A.decommit(d); 
      return Ver pk (m', (c', d'))
             /\ rel m m' /\ (c,d) <> (c',d');
  }
}.




local lemma qq &m h :
  Pr[ SNM_G0'(H(A)).main(h) @ &m : res ]
 =   Pr[ SNM_G0z(H(A)).main(h) @ &m : res ].
proof. byequiv (_: ={glob A, arg} ==> _) =>//. 
proc. inline*.  sim. wp. rnd. wp. call (_:true).
wp. rnd. skip. progress. 
qed.



local lemma pp &m h :
 Pr[ SNM_G0z(H(A)).main(h) @ &m : res ]
 = Pr[ SNM_G0y(H(A)).main(h) @ &m : res ].
proof. byequiv =>//.
proc. sim.  call q1q2. inline*. wp. call (_:true). wp.
rnd. skip. progress. 
qed.


local module MyTail(A : AdvSNM) = {
  var c,c' : commitment
  var d,d' : openingkey
  proc main(b : bool, h : advice) = {
    var pk, m', rs, md, m, rel;
    pk                 <$ Dpk;
    (md, rel)                 <- A.init(pk,h);
    m                  <- if b then H.m2 else H.m1;
    rs                 <$ rndstr;
    (c, d)             <- Com pk rs m;
    c'                 <- A.commit(c, rel);
    (d', m')           <- A.decommit(d); 
      return Ver pk (m', (c', d'))
             /\ rel m m' /\ (c,d) <> (c',d');    
  }
}.

local module MyTail'(A : AdvSNM) = {
  var c,c' : commitment
  var d,d' : openingkey
  proc main(b : bool, h : advice) = {
    var pk, m', rs, md, m, rel;
    pk                 <$ Dpk;
    (md, rel)                 <- A.init(pk,h);
    m                  <- if b then H.m2 else H.m1;
    rs                 <$ rndstr;
    (c, d)             <- Com pk rs m;
    c'                 <- A.commit(c, rel);
    (d', m')           <- A.decommit(d); 
      return (c,d) = (c',d');    
  }
}.



local lemma dd &m h :
 Pr[ SNM_G0y(H(A)).main(h) @ &m : res ]
 = Pr[ W(MyTail(H(A))).main(h) @ &m : res ].
proof. byequiv => //. proc. 
inline*. wp. rnd.  call (_:true).
wp. rnd.  wp.  swap {1} 9 -8.  wp.  call (_:true).
wp.  rnd. wp.  rnd. skip. progress. smt. smt. 
qed.


local lemma mysplitcases &m h :
    Pr[ W(MyTail(H(A))).main(h) @ &m : res ]
   = Pr[ MyTail(H(A)).main(false, h) @ &m : res ] / 2%r
   + Pr[ MyTail(H(A)).main(true,h)  @ &m : res ] / 2%r.
proof. 
apply (splitcases (MyTail(H(A)))).
qed.


local lemma mysplitcases' &m h :
    Pr[ W(MyTail'(H(A))).main(h) @ &m : res ]
   = Pr[ MyTail'(H(A)).main(false, h) @ &m : res ] / 2%r
   + Pr[ MyTail'(H(A)).main(true,h)  @ &m : res ] / 2%r.
proof. 
apply (splitcases (MyTail'(H(A)))).
qed.


local lemma kk &m h : 
 Pr[ HEPT0(A).main() @ &m : res = false /\ HEP.m1 <> HEP.m2 ] <=
 Pr[ MyTail(H(A)).main(false, h) @ &m : res /\ H.m1 <> H.m2 ] +
 Pr[ MyTail(H(A)).main(false, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ].
proof. byequiv =>//.
proc. 
wp.  inline*. wp. rnd {2}. wp. call (_:true). wp.
rnd. wp.  call (_:true). wp. rnd. skip. progress.
smt. smt. smt. 
qed.


local lemma kkk &m h : 
 Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ] <=
    Pr[ MyTail(H(A)).main(true, h) @ &m : res /\ H.m1 <> H.m2 ] + 
  Pr[ MyTail(H(A)).main(true, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ].
proof. 
have ->: Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 <>  HEP.m2 ] =
  Pr[ HEPT1(A).main() @ &m : res = true /\  HEP.m1 <> HEP.m2 ].
rewrite Pr[mu_eq]. smt. auto.
byequiv =>//.
proc. inline*. 
wp. rnd {2}. wp. call (_:true). 
wp. rnd. wp. call (_:true). wp. rnd.
skip. progress. smt. smt. smt. 
qed.



local lemma ssf1 &m : 
 Pr[ HEPT1(A).main() @ &m : res ] - Pr[ HEPT0(A).main() @ &m : res ] 
  = Pr[ HEPT0(A).main() @ &m : res = false /\ HEP.m1 <> HEP.m2 ] 
    + Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ]
    - Pr[ HEPT0(A).main() @ &m : HEP.m1 <> HEP.m2 ].
proof. 
have ->: Pr[HEPT0(A).main() @ &m : res = false /\ HEP.m1 <> HEP.m2]
 = Pr[HEPT0(A).main() @ &m : res = false].
 have ->: Pr[HEPT0(A).main() @ &m : res = false] 
          = Pr[HEPT0(A).main() @ &m : res = false /\ HEP.m1 <> HEP.m2]
          + Pr[HEPT0(A).main() @ &m : res = false /\ HEP.m1 = HEP.m2].
  rewrite Pr[mu_split HEP.m1 = HEP.m2]. smt.
 have z : Pr[HEPT0(A).main() @ &m : res = false /\ HEP.m1 = HEP.m2] <= 0%r.
 rewrite - (qq1_impl &m). rewrite Pr[mu_sub]. auto. auto. 
smt.
have ->: Pr[HEPT1(A).main() @ &m : res /\ HEP.m1 <> HEP.m2]
 = Pr[HEPT1(A).main() @ &m : res ].
 have ->: Pr[HEPT1(A).main() @ &m : res ] 
          = Pr[HEPT1(A).main() @ &m : res /\ HEP.m1 <> HEP.m2]
          + Pr[HEPT1(A).main() @ &m : res /\ HEP.m1 = HEP.m2].
  rewrite Pr[mu_split HEP.m1 = HEP.m2]. smt.
 have z : Pr[HEPT1(A).main() @ &m : res /\ HEP.m1 = HEP.m2] <= 0%r.
 rewrite - (qq2_impl &m). rewrite Pr[mu_sub]. auto. auto. 
smt. 
rewrite qq1.
have <-: Pr[HEPT0(A).main() @ &m : true ] = 1%r.
smt.
have ->: Pr[HEPT0(A).main() @ &m : true]
 = Pr[HEPT0(A).main() @ &m : res ] + Pr[HEPT0(A).main() @ &m : res = false ].
rewrite Pr[mu_split res]. smt.
smt.
qed.
 


lemma obv (a b c d : real) : a <= c /\ b <= d =>  (a + b) - 1%r <= (c + d) - 1%r.
proof. smt.
qed.


local lemma ssf3 &m h : 
 Pr[MyTail(H(A)).main(false, h) @ &m :  H.m1 = H.m2]
 = Pr[ HEPT0(A).main() @ &m : HEP.m1 = HEP.m2 ].
proof. byequiv =>//.  proc. inline*. wp. rnd{1}. wp. call (_:true).
wp.  rnd. wp.  call (_:true). wp.  rnd. skip. progress. smt.
qed.


local lemma ssf4 &m h : 
 Pr[MyTail(H(A)).main(true, h) @ &m :  H.m1 = H.m2]
 = Pr[ HEPT1(A).main() @ &m : HEP.m1 = HEP.m2 ].
proof. byequiv =>//.  proc. inline*. wp. rnd{1}. wp. call (_:true).
wp.  rnd. wp.  call (_:true). wp.  rnd. skip. progress. smt. 
qed.

local lemma ssf2 &m h : 
 1%r/2%r * (Pr[ HidingExperiment1(A).main() @ &m : res ] - Pr[ HidingExperiment0(A).main() @ &m : res ]) 
 <= Pr[ SG0(H(A)).main(h) @ &m : res ] - 1%r/2%r
 + Pr[ MyTail(H(A)).main(false, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ] / 2%r
 + Pr[ MyTail(H(A)).main(true, h) @ &m  : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ] / 2%r.
proof.
have ->: Pr[ SG0(H(A)).main(h) @ &m : res ]
 = Pr[ SNM_G0'(H(A)).main(h) @ &m : res ].
byequiv =>//. sim. 
have ->: Pr[ SNM_G0'(H(A)).main(h) @ &m : res ] = 
 Pr[  W(MyTail(H(A))).main(h) @ &m : res ].
rewrite - (dd &m h). rewrite (qq &m h).
rewrite  (pp &m h) =>//. 
have <-: Pr[ HEPT0(A).main() @ &m : res ]
 = Pr[ HidingExperiment0(A).main() @ &m : res ].
byequiv =>//. sim.
have <-: Pr[ HEPT1(A).main() @ &m : res ]
 = Pr[ HidingExperiment1(A).main() @ &m : res ].
byequiv =>//. sim. 
rewrite mysplitcases ssf1 qq1.
have ->: Pr[MyTail(H(A)).main(false, h) @ &m : res]
  = Pr[MyTail(H(A)).main(false, h) @ &m : res /\ H.m1 <> H.m2 ].
rewrite Pr[mu_split H.m1 = H.m2].
have ->: Pr[MyTail(H(A)).main(false, h) @ &m : res /\ H.m1 = H.m2] = 0%r.
  have f: Pr[MyTail(H(A)).main(false, h) @ &m : res /\ H.m1 = H.m2] <=
    Pr[MyTail(H(A)).main(false, h) @ &m : H.m1 = H.m2]. rewrite Pr[mu_sub]. smt.
  auto. 
  have ff : Pr[MyTail(H(A)).main(false, h) @ &m : H.m1 = H.m2] = 0%r.
  rewrite ssf3. apply qq1_impl. smt. 
simplify. auto.
have ->: Pr[MyTail(H(A)).main(true, h) @ &m : res]
  = Pr[MyTail(H(A)).main(true, h) @ &m : res /\ H.m1 <> H.m2 ].
rewrite Pr[mu_split H.m1 = H.m2].
  have ->: Pr[MyTail(H(A)).main(true, h) @ &m : res /\ H.m1 = H.m2] = 0%r.
  have f: Pr[MyTail(H(A)).main(true, h) @ &m : res /\ H.m1 = H.m2] <=
    Pr[MyTail(H(A)).main(true, h) @ &m : H.m1 = H.m2]. rewrite Pr[mu_sub]. smt.
  auto. 
  have ff : Pr[MyTail(H(A)).main(true, h) @ &m : H.m1 = H.m2] = 0%r.
  rewrite ssf4. apply qq2_impl. smt. 
simplify. auto.  
have f1 : Pr[HEPT0(A).main() @ &m : res = false /\ HEP.m1 <> HEP.m2]
 <= Pr[MyTail(H(A)).main(false, h) @ &m : res /\ H.m1 <> H.m2 ]
 + Pr[ MyTail(H(A)).main(false, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ].
 apply (kk &m).
have f2 : Pr[HEPT1(A).main() @ &m : res /\ HEP.m1 <> HEP.m2]
 <= Pr[MyTail(H(A)).main(true, h) @ &m : res /\ H.m1 <> H.m2 ]
 + Pr[ MyTail(H(A)).main(true, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ].
 apply (kkk &m).
have ->: Pr[MyTail(H(A)).main(false, h) @ &m : res /\ H.m1 <> H.m2] / 2%r +
Pr[MyTail(H(A)).main(true, h) @ &m : res /\ H.m1 <> H.m2] / 2%r - 1%r / 2%r +
Pr[MyTail(H(A)).main(false, h) @ &m :
   (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')] / 2%r +
Pr[MyTail(H(A)).main(true, h) @ &m :
   (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')] / 2%r
 = (1%r/2%r) * 
   (Pr[MyTail(H(A)).main(false, h) @ &m : res /\ H.m1 <> H.m2]  +
Pr[MyTail(H(A)).main(true, h) @ &m : res /\ H.m1 <> H.m2]  - 1%r +
Pr[MyTail(H(A)).main(false, h) @ &m :
   (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')]  +
Pr[MyTail(H(A)).main(true, h) @ &m :
   (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')]).
smt.
have ->: Pr[MyTail(H(A)).main(false, h) @ &m : res /\ H.m1 <> H.m2] +
 Pr[MyTail(H(A)).main(true, h) @ &m : res /\ H.m1 <> H.m2] - 1%r +
 Pr[MyTail(H(A)).main(false, h) @ &m :
    (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')] +
 Pr[MyTail(H(A)).main(true, h) @ &m :
    (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')]
 = 
  (Pr[MyTail(H(A)).main(false, h) @ &m : res /\ H.m1 <> H.m2] +
  Pr[MyTail(H(A)).main(false, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')])
 +   (Pr[MyTail(H(A)).main(true, h) @ &m : res /\ H.m1 <> H.m2] +
  Pr[MyTail(H(A)).main(true, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')])
 - 1%r.
smt.
have : (Pr[HEPT0(A).main() @ &m : res = false /\ HEP.m1 <> HEP.m2] +
 Pr[HEPT1(A).main() @ &m : res /\ HEP.m1 <> HEP.m2] - 1%r) <=
(Pr[MyTail(H(A)).main(false, h) @ &m : res /\ H.m1 <> H.m2] +
 Pr[MyTail(H(A)).main(false, h) @ &m :
    (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')] +
 (Pr[MyTail(H(A)).main(true, h) @ &m : res /\ H.m1 <> H.m2] +
  Pr[MyTail(H(A)).main(true, h) @ &m :
     (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')]) -
 1%r).
apply obv. split.
apply f1.
apply f2.
smt.
qed.



require import StdOrder.
import RealOrder.

local lemma nsnm_pure_hiding' &m h : forall (S <: Simulator {H, A}),
 1%r/2%r * (Pr[ HidingExperiment1(A).main() @ &m : res ] - Pr[ HidingExperiment0(A).main() @ &m : res ]) 
 <= Pr[ SG0(H(A)).main(h) @ &m : res ] - Pr[ SG1(H(A),S).main(h) @ &m : res ]
 + Pr[ MyTail(H(A)).main(false, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ] / 2%r
 + Pr[ MyTail(H(A)).main(true, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ] / 2%r.
proof. move => S.
have f1 :  1%r/2%r * (Pr[ HidingExperiment1(A).main() @ &m : res ] - Pr[ HidingExperiment0(A).main() @ &m : res ]) 
 <= Pr[ SG0(H(A)).main(h) @ &m : res ] - 1%r/2%r
 + Pr[ MyTail(H(A)).main(false, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ] / 2%r
 + Pr[ MyTail(H(A)).main(true, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ] / 2%r.
apply ssf2.
have f2 : Pr[ SG1(H(A), S).main(h) @ &m : res ] <= 1%r/2%r.
have ->: Pr[ SG1(H(A), S).main(h) @ &m : res ] = Pr[ SNM_G1'(H(A), S).main(h) @ &m : res ].
byequiv =>//. sim. apply (game1 &m h S).
have f3: 
 Pr[SG0(H(A)).main(h) @ &m : res] - 1%r/2%r +
   Pr[MyTail(H(A)).main(false, h) @ &m :
      (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')] / 2%r +
   Pr[MyTail(H(A)).main(true, h) @ &m :
     (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')] / 2%r
  <=
 Pr[SG0(H(A)).main(h) @ &m : res] - Pr[SG1(H(A), S).main(h) @ &m : res] +
   Pr[MyTail(H(A)).main(false, h) @ &m :
      (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')] / 2%r +
   Pr[MyTail(H(A)).main(true, h) @ &m :
     (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')] / 2%r.
smt.
apply (ler_trans (Pr[SG0(H(A)).main(h) @ &m : res] - 1%r/2%r +
   Pr[MyTail(H(A)).main(false, h) @ &m :
      (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')] / 2%r +
   Pr[MyTail(H(A)).main(true, h) @ &m :
     (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')] / 2%r)). apply f1.
apply f3.
qed.


module HG(U : Unhider) = {
  proc guess(pk : value) : message * (commitment * openingkey) list = {
    var rs,m,m1,m2,c1,c2,d1,d2,b;
    (m1,m2) <@ U.choose(pk);
    b                  <$ {0,1};
    m <- if b then m2 else m1;
    rs <$ rndstr;
    (c1,d1) <- Com pk rs m1; 
    (c2,d2) <- Com pk rs m2;     
    return (m , [(c1,d1); (c2,d2)]);
  }
}.


local module HG'(U : Unhider) = {
  proc main() :bool = {
    var rs,m,m1,m2,c1,c2,d1,d2,b;
    var pk,c',d',rs0;
    b                  <$ {0,1};
    pk                 <$ Dpk;


    (m1,m2) <@ U.choose(pk);
    m <- if b then m2 else m1;
    rs <$ rndstr;
    (c1,d1) <- Com pk rs m1; 
    (c2,d2) <- Com pk rs m2;     
    rs0 <$ rndstr;
    (c', d')             <- Com pk rs0 m;
    return (c',d') \in ([(c1,d1); (c2,d2)]);
  }
}.



local lemma guessprob &m h : 
 Pr[ MyTail(H(A)).main(false, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ] / 2%r
   + Pr[ MyTail(H(A)).main(true,h)  @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ] / 2%r
  <= Pr[ UnpredGame(HG(A)).main() @ &m : res ].
proof.   
have ->: 
 Pr[ MyTail(H(A)).main(false, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ] / 2%r
   + Pr[ MyTail(H(A)).main(true,h)  @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ] / 2%r
 =     Pr[ W(MyTail(H(A))).main(h) @ &m :  (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ].    
  have ->: Pr[ MyTail(H(A)).main(false, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ]
   = Pr[ MyTail'(H(A)).main(false, h) @ &m : res ]. 
   byequiv (_: ={glob A, glob H, glob MyTail, arg} ==> ((MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')){1} 
     = res{2} ) =>//. proc. sim. 
  have ->: Pr[ MyTail(H(A)).main(true, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ]
   = Pr[ MyTail'(H(A)).main(true, h) @ &m : res ]. 
   byequiv (_: ={glob A, glob H, glob MyTail, arg} ==> ((MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')){1} 
     = res{2} )=>//. proc. sim.   have ->: Pr[ W(MyTail(H(A))).main(h) @ &m :  (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ]
   = Pr[ W(MyTail'(H(A))).main(h) @ &m :  res ].
   byequiv (_: ={glob A, glob H, glob MyTail, arg} ==> ((MyTail.c, MyTail.d) = (MyTail.c', MyTail.d')){1} 
     = res{2} ) =>//. proc.  inline*. wp.  simplify. sim.  
rewrite (mysplitcases' &m h) =>//. 
have ->: Pr[ UnpredGame(HG(A)).main() @ &m : res ]
 = Pr[ HG'(A).main() @ &m : res ].
byequiv (_: ={glob A}  ==> _) =>//. proc.  inline*. swap {1} 4 -3.  wp. 
rnd. wp.  rnd. wp.  call (_:true).  wp. rnd. rnd. skip. progress. 
byequiv (_: ={glob A}  ==> _) =>//.
proc. inline*. simplify. swap {2} [8..9] -3.
wp. rnd. wp.  call {1} Ag_ll. wp. rnd. wp.
call (_:true). wp.  rnd.  wp. rnd. skip. progress. 
 smt. smt. 
qed.



lemma snnm_pure_hiding1 &m h : forall (S <: Simulator {H, A}),
 (Pr[ HidingExperiment1(A).main() @ &m : res ] - Pr[ HidingExperiment0(A).main() @ &m : res ]) 
 <= 2%r * (Pr[ SG0(H(A)).main(h) @ &m : res ] - Pr[ SG1(H(A),S).main(h) @ &m : res ]
 + Pr[ UnpredGame(HG(A)).main() @ &m : res ]).
proof. move => S.
have q : 1%r/2%r * (Pr[ HidingExperiment1(A).main() @ &m : res ] - Pr[ HidingExperiment0(A).main() @ &m : res ]) 
 <= Pr[ SG0(H(A)).main(h) @ &m : res ] - Pr[ SG1(H(A),S).main(h) @ &m : res ]
 + Pr[ MyTail(H(A)).main(false, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ] / 2%r
 + Pr[ MyTail(H(A)).main(true, h) @ &m : (MyTail.c, MyTail.d) = (MyTail.c', MyTail.d') ] / 2%r.
apply (nsnm_pure_hiding' &m h S) .   
smt.
qed.
end section.


module F(A : Unhider) = {
  proc choose(pk : value)   = {
    var m1,m2;
    (m1,m2) <- A.choose(pk);
    return (m1,m2);
  }

  proc guess(c : commitment) = {
    var r;
    r <- A.guess(c);
    return !r;
  }
}.






section.
declare module A : Unhider {H, HEPT0,HEPT1}.


axiom a1 :  islossless A.guess.
axiom a2:  islossless A.choose.
axiom a3 : forall &m, Pr[HEPT0(A).main() @ &m : HEP.m1 <> HEP.m2] = 1%r.
axiom a4 : forall &m, Pr[HEPT1(A).main() @ &m : HEP.m1 <> HEP.m2] = 1%r.
axiom a5:  phoare[ A.choose : true ==> res.`1 <> res.`2] = 1%r.
axiom a6 : islossless A.guess.

local lemma fl1 &m : Pr[ HidingExperiment0(F(A)).main() @ &m : res ] = Pr[ HidingExperiment0(A).main() @ &m : !res ].
proof. byequiv =>//. proc. inline*. wp. call (_:true).
wp.  rnd. wp.  call (_:true). wp. rnd. skip. progress. 
qed.

local lemma fl11 &m : Pr[ HidingExperiment0(F(A)).main() @ &m : res ] = 1%r - Pr[ HidingExperiment0(A).main() @ &m : res ].
proof. rewrite fl1 Pr[mu_not]. 
have ->: Pr[HidingExperiment0(A).main() @ &m : true] = 1%r.
byphoare =>//. proc. call a6. wp.  rnd.  call a2. rnd. skip.  smt. auto.
qed.


local lemma fl2 &m : Pr[ HidingExperiment1(F(A)).main() @ &m : res ] = Pr[ HidingExperiment1(A).main() @ &m : !res ].
proof. byequiv =>//. proc. inline*. wp. call (_:true).
wp.  rnd. wp.  call (_:true). wp. rnd. skip. progress. 
qed.

local lemma fl22 &m : Pr[ HidingExperiment1(F(A)).main() @ &m : res ] = 1%r - Pr[ HidingExperiment1(A).main() @ &m : res ].
proof. rewrite fl2 Pr[mu_not]. 
have ->: Pr[HidingExperiment1(A).main() @ &m : true] = 1%r.
byphoare =>//. proc. call a6. wp.  rnd.  call a2. rnd. skip.  smt. auto. 
qed.

local lemma fl3 &m : Pr[ HidingExperiment1(F(A)).main() @ &m : res ] 
 - Pr[ HidingExperiment0(F(A)).main() @ &m : res ] = - (Pr[ HidingExperiment1(A).main() @ &m : res ] - 
  Pr[ HidingExperiment0(A).main() @ &m : res ] ).
proof. smt.
qed.

op maxr (a b : real) = if a < b then b else a.

local lemma snnm_pure_hiding2 &m h : forall (S <: Simulator {H, A}),
 (Pr[ HidingExperiment1(F(A)).main() @ &m : res ] - Pr[ HidingExperiment0(F(A)).main() @ &m : res ]) 
 <= 2%r * (Pr[ SG0(H(F(A))).main(h) @ &m : res ] - Pr[ SG1(H(F(A)),S).main(h) @ &m : res ]
 + Pr[ UnpredGame(HG(F(A))).main() @ &m : res ]).
proof. move => S.  
have fa1 : phoare[ F(A).guess : true ==> true] = 1%r. 
proc. call a1. auto.
have fa2:  phoare[ F(A).choose : true ==> true] = 1%r. 
proc. call a2. auto.
have fa3 : forall &m, Pr[HEPT0(F(A)).main() @ &m : HEP.m1 <> HEP.m2] = 1%r. 
move => &m0.
have ->: Pr[HEPT0(F(A)).main() @ &m0 : HEP.m1 <> HEP.m2] = Pr[HEPT0(A).main() @ &m0 : HEP.m1 <> HEP.m2].
byequiv =>//. proc.  inline*. wp. call (_:true). wp. rnd.  wp. call (_:true). wp. rnd. skip. progress. apply a3.
have fa4 : forall &m, Pr[HEPT1(F(A)).main() @ &m : HEP.m1 <> HEP.m2] = 1%r. 
move => &m0.
have ->: Pr[HEPT1(F(A)).main() @ &m0 : HEP.m1 <> HEP.m2] = Pr[HEPT1(A).main() @ &m0 : HEP.m1 <> HEP.m2].
byequiv =>//. proc.  inline*. wp. call (_:true). wp. rnd.  wp. call (_:true). wp. rnd. skip. progress. apply a4.
have fa5:  phoare[ F(A).choose : true ==> res.`1 <> res.`2] = 1%r. 
proc. call a5. skip. auto.
apply (snnm_pure_hiding1 (F(A)) fa1 fa2 fa3 fa4 fa5 &m h S).     
qed.
 

lemma nsnm_pure_hiding &m h : forall (S <: Simulator {H, A}),
 `|Pr[ HidingExperiment1(F(A)).main() @ &m : res ] - Pr[ HidingExperiment0(F(A)).main() @ &m : res ]|
 <= maxr
      (2%r * (Pr[ SG0(H(A)).main(h) @ &m : res ] - Pr[ SG1(H(A),S).main(h) @ &m : res ]
           + Pr[ UnpredGame(HG(A)).main() @ &m : res ]))
      (2%r * (Pr[ SG0(H(F(A))).main(h) @ &m : res ] - Pr[ SG1(H(F(A)),S).main(h) @ &m : res ]
           + Pr[ UnpredGame(HG(F(A))).main() @ &m : res ])) .
proof. move => S.
    have b1 : (Pr[ HidingExperiment1(A).main() @ &m : res ] - Pr[ HidingExperiment0(A).main() @ &m : res ]) 
 <= 2%r * (Pr[ SG0(H(A)).main(h) @ &m : res ] - Pr[ SG1(H(A),S).main(h) @ &m : res ]
 + Pr[ UnpredGame(HG(A)).main() @ &m : res ]).
  apply (snnm_pure_hiding1 A a1 a2 a3 a4 a5 &m h S).     
    have b2 : (Pr[ HidingExperiment1(F(A)).main() @ &m : res ] - Pr[ HidingExperiment0(F(A)).main() @ &m : res ]) 
 <= 2%r * (Pr[ SG0(H(F(A))).main(h) @ &m : res ] - Pr[ SG1(H(F(A)),S).main(h) @ &m : res ]
 + Pr[ UnpredGame(HG(F(A))).main() @ &m : res ]).
  apply (snnm_pure_hiding2 &m h S). 
smt.
qed.

end section.
