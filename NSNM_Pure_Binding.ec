pragma Goals:printall.
require import DBool List Real.
require import Commitment.
require import Distr AllCore.



require import D1D2.
require import NSNM_Definition.

require CommitmentUnpredictability.



theory NSNM_binding_theory.


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


axiom S_inj pk m1 m2 c2 d2 r :  pk \in Dpk =>
  m1 <> m2 => (c2, d2) = Com pk r m2 =>
  Ver pk (m1, (c2, d2)) = false.


module BindingExperiment(A:Binder) = {
  proc main()  = {
      var m,m',x, c, d, d';
      x                 <$ Dpk;
      (c, m, d, m', d') <@ A.bind(x);
      return Ver x (m,  (c, d)) /\ Ver x (m', (c, d')) /\ (m <> m');        
  }
}.

(* transformation of a binder-adversary into NM-adversary *)
module B(U : Binder) = {
  var m1, m2, m3 : message
  var pk : value
  var c,c',c3 : commitment
  var d1,d2,d3 : openingkey
  var vers : bool

  proc init(y : value, h : advice) = {
    pk <- y;
    (c,m1,d1,m2,d2) <@ U.bind(pk);
    vers <- Ver pk (m1,  (c, d1)) /\ Ver pk (m2,  (c, d2)) /\ m1 <> m2;
    return (duniform [m1;m2], fun (m1 m2 : message) => m1 = m2);
  }

  proc commit(z : commitment, r : snm_relation) : commitment  = {
    var rs;
    c' <- z;
    rs <$ rndstr;
    (c3,d3) <- Com pk rs m1;   
    return (if vers then c else c3);
  }

  proc decommit(d' : openingkey) : openingkey * message = {
      return  if vers then (if Ver pk (m1, (c',d'))
                 then (d1,m1)
                 else (d2,m2)) else (d3,m1);
  }
}.


(* transformation of a binder-adversary into unpredictability adversary *)
module BG(U : Binder) = {
  proc guess(pk : value) : message * (commitment * openingkey) list = {
    var rs,m,m1,m2,c,c3,d1,d2,d3;
    (c,m1,d1,m2,d2) <@ U.bind(pk);
    m                  <$ duniform [m1;m2];
    rs <$ rndstr;
    (c3,d3) <- Com pk rs m1;   
    return (m , [(c,d1); (c,d2); (c3,d3)]);
  }
}.


module G0(A : AdvSNM) = {
  var m,m' : message
  var c, c' : commitment
  var d, d' : openingkey
  proc main(h : advice) : bool = {
    var pk, rs, md, rel;
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



module G1(A : AdvSNM, S : Simulator) = {
  proc main(h : advice) : bool = {
    var pk, m, c', d', m', md, mrel;    
    pk                 <$ Dpk; 
    (md, mrel)         <- A.init(pk,h);
    m                  <$ md;
    (m', c',  d')      <- S.simulate(pk, mrel);
    return mrel m m';
  }
}.



section.

local module BEP(A:Binder) = {
  var m,m' : message
  proc main()  = {
      var x, c, d, d';
      x                 <$ Dpk;
      (c, m, d, m', d') <@ A.bind(x);
      return Ver x (m,  (c, d)) /\ Ver x (m', (c, d')) /\ (m <> m');        
  }
}.


declare module A : Binder {G0, B}.

axiom Ag_ll : islossless A.bind.
(* the adversaries who return same message twice do not win the binding game *)
axiom ba : hoare [ A.bind : true ==> res.`2 <> res.`4 ]. 


local lemma ss &m h : Pr[G0(B(A)).main(h) @ &m : true ] = 1%r.
proof. byphoare.
proc. inline*. wp. rnd. 
conseq (_: _ ==> true). smt.
wp.  rnd. 
conseq (_: _ ==> true). smt.
rnd. 
simplify.
wp. 
call Ag_ll. wp. rnd.
skip. progress. smt.
smt. auto. auto.
qed.



local lemma step1 &m h : 
  Pr[ G0(B(A)).main(h) @ &m : B.vers  /\ (G0.c, G0.d) <>  (G0.c', G0.d')  ]
   = Pr[ G0(B(A)).main(h) @ &m : res /\ B.vers  /\ (G0.c, G0.d) <>  (G0.c', G0.d')  ]. 
proof. byequiv. 
proc. inline*. wp. rnd. wp.
rnd.  rnd. wp. call (_:true). wp. rnd. 
  skip. progress. smt. smt.
auto. auto.
qed.

local lemma step2 &m h : 
  Pr[ BEP(A).main() @ &m : res ] 
   = Pr[ G0(B(A)).main(h) @ &m : B.vers ].
proof. byequiv.
proc. inline*. wp. rnd {2}. wp. rnd{2}. rnd{2}.
wp. call (_:true). wp.  rnd. skip. progress. smt. smt.  auto. auto.
qed.




local module G5 = {
  var m,m' : message
  var c, c' : commitment
  var d, d' : openingkey
  module B = B(A)

  proc bra() = {
    B.pk                 <$ Dpk;
    (B.c,B.m1,B.d1,B.m2,B.d2) <@ A.bind(B.pk);
    B.vers <- Ver B.pk (B.m1,  (B.c, B.d1))
        /\ Ver B.pk (B.m2,  (B.c, B.d2)) /\ B.m1 <> B.m2;
  }

  proc main(h : advice) : bool = {
    var  rs;
    bra();
    m                  <$ duniform [B.m1; B.m2] ;
    rs                 <$ rndstr;
    (c, d)             <- Com B.pk rs m;
    c'                 <- B.commit(c, fun (m1 m2 : message) => m1 = m2);
    (d', m')           <- B.decommit(d); 
      return Ver B.pk (m', (c', d'))
             /\  m = m' /\ (c,d) <> (c',d');
  }
}.

local lemma jkk &m h : 
  Pr[ G5.main(h) @ &m : !B.vers /\ G5.m = G5.m' ]
 =  Pr[ G5.main(h) @ &m : !B.vers ] * 1%r/2%r .
byphoare (_: (glob A) = (glob A){m} ==> _). proc. 
inline B(A).commit. 
inline B(A).decommit. wp. 
conseq (_: _ ==> !B.vers /\ G5.m = B.m1). smt. 
inline B(A).init.
pose z := Pr[ G5.main(h) @ &m : !B.vers ].
seq 1 : (!B.vers) z (1%r/2%r)  (1%r/2%r) 0%r ( B.m1 <> B.m2). 
inline*. wp. call ba. wp. rnd. skip. auto.
have phr : phoare[ G5.bra : (glob A) = (glob A){m}  ==> !B.vers ]
             = Pr[G5.main(h) @ &m : !B.vers].
bypr. progress. byequiv. proc.
inline*. wp. rnd{2}. wp. rnd{2}. rnd{2}. wp.
call (_:true). rnd.  skip. progress. auto. auto.  smt.
smt. auto.  auto.
call phr. skip.  auto.
rnd. 
conseq (_: _ ==> (!B.vers /\ G5.m = B.m1)). smt.
wp. rnd. conseq (_: _ ==> (!B.vers /\ G5.m = B.m1)). smt.
rnd. wp. skip. progress. rewrite H0. simplify.
rewrite duniform1E. smt.
simplify.
hoare. rnd.  wp.  rnd. rnd. wp.  skip. progress. 
smt. smt. auto. auto.
qed.

local lemma jkk2 &m h : 
  Pr[ G5.main(h) @ &m : !B.vers /\ G5.m = G5.m' ]
 = Pr[ G0(B(A)).main(h) @ &m : !B.vers /\ G0.m = G0.m' ].
proof. byequiv. proc. sim.  inline*. wp.  rnd. wp. 
rnd. rnd. wp. call (_:true).
wp.  rnd. skip. progress. auto. auto.
qed.


local lemma jkk3 &m h :  
 Pr[ G5.main(h) @ &m : !B.vers ]
 = Pr[ G0(B(A)).main(h) @ &m : !B.vers  ].
proof. byequiv. proc. sim.  inline*. wp.  
rnd. wp. rnd. rnd. wp. call (_:true).
wp.  rnd. skip. progress. auto. auto.
qed.


local lemma jkk_fin &m h : 
  1%r/2%r  * Pr[ G0(B(A)).main(h) @ &m : !B.vers ] 
  = Pr[ G0(B(A)).main(h) @ &m : !B.vers /\ G0.m = G0.m' ].
smt.
qed.



local lemma step3 &m  h:  
    Pr[ G0(B(A)).main(h) @ &m : res /\ !B.vers ] 
  = 1%r/2%r * Pr[ G0(B(A)).main(h) @ &m : !B.vers ] 
  - Pr[ G0(B(A)).main(h) @ &m : !B.vers /\ G0.m = G0.m' 
        /\ (G0.c,G0.d) = (G0.c',G0.d') ].
proof. 
have ->: 1%r/2%r * Pr[ G0(B(A)).main(h) @ &m : !B.vers ] 
 = Pr[ G0(B(A)).main(h) @ &m : !B.vers /\ G0.m = G0.m' ].
apply jkk_fin.  
have ->: Pr[G0(B(A)).main(h) @ &m : !B.vers /\ G0.m = G0.m']
 = Pr[G0(B(A)).main(h) @ &m : !B.vers /\ G0.m = G0.m' 
          /\ (G0.c, G0.d) = (G0.c', G0.d')]  
 + Pr[G0(B(A)).main(h) @ &m : !B.vers /\ G0.m = G0.m' 
          /\ (G0.c, G0.d) <> (G0.c', G0.d')].
rewrite Pr[mu_split (G0.c, G0.d) = (G0.c', G0.d')].
  have ->: Pr[G0(B(A)).main(h) @ &m :
   (!B.vers /\ G0.m = G0.m') /\ (G0.c, G0.d) = (G0.c', G0.d')]
  = Pr[G0(B(A)).main(h) @ &m :
   !B.vers /\ G0.m = G0.m' /\ (G0.c, G0.d) = (G0.c', G0.d')].
 rewrite Pr[mu_eq]. auto. auto.
  have ->: Pr[G0(B(A)).main(h) @ &m :
   (!B.vers /\ G0.m = G0.m') /\ (G0.c, G0.d) <> (G0.c', G0.d')]
   = Pr[G0(B(A)).main(h) @ &m :
   !B.vers /\ G0.m = G0.m' /\ (G0.c, G0.d) <> (G0.c', G0.d')].
  rewrite Pr[mu_eq]. auto. auto. auto.  
have ->: Pr[G0(B(A)).main(h) @ &m :
   !B.vers /\ G0.m = G0.m' /\ (G0.c, G0.d) <> (G0.c', G0.d')]
  = Pr[G0(B(A)).main(h) @ &m : res /\ !B.vers].
byequiv.  proc. 
inline*. wp. rnd. wp. rnd. rnd. wp. 
call (_:true). wp. rnd. skip. progress.
smt. smt. smt. auto. auto. smt.
qed.



local lemma zzz (a b c : real) : a <= c =>
 a - b <= c - b. smt. qed.  

local lemma step6 &m h: 
 1%r/2%r * Pr[ BEP(A).main() @ &m : res ]
 - 2%r * Pr[ G0(B(A)).main(h) @ &m : B.vers /\ (G0.c,G0.d) = (G0.c',G0.d') ] 
 <= Pr[ G0(B(A)).main(h) @ &m : res ] - 1%r/2%r
 + Pr[ G0(B(A)).main(h) @ &m : !B.vers /\ G0.m = G0.m' /\ (G0.c,G0.d) = (G0.c',G0.d') ].
have ->: 
 Pr[ G0(B(A)).main(h) @ &m : res ]
 =  Pr[ G0(B(A)).main(h) @ &m : res /\ B.vers ]
 + Pr[ G0(B(A)).main(h) @ &m : res /\ !B.vers ].
rewrite Pr[mu_split B.vers]. auto.
have ->: Pr[ G0(B(A)).main(h) @ &m : res /\ !B.vers ]
 = 1%r/2%r * Pr[ G0(B(A)).main(h) @ &m : !B.vers ]
 -  Pr[ G0(B(A)).main(h) @ &m : !B.vers /\ G0.m = G0.m' /\ (G0.c,G0.d) = (G0.c',G0.d') ].
apply step3.
have ->: Pr[G0(B(A)).main(h) @ &m : res /\ B.vers]
 = Pr[ G0(B(A)).main(h) @ &m : res /\ B.vers /\ (G0.c,G0.d) = (G0.c',G0.d') ]
 + Pr[ G0(B(A)).main(h) @ &m : res /\ B.vers /\ (G0.c,G0.d) <> (G0.c',G0.d') ].
rewrite Pr[mu_split (G0.c,G0.d) = (G0.c',G0.d')]. 
  have ->: 
   Pr[G0(B(A)).main(h) @ &m : (res /\ B.vers) /\ (G0.c, G0.d) = (G0.c', G0.d')]
   = Pr[G0(B(A)).main(h) @ &m : res /\ B.vers /\ (G0.c, G0.d) = (G0.c', G0.d')].
  rewrite Pr[mu_eq]. auto. auto.
  have ->: Pr[G0(B(A)).main(h) @ &m : (res /\ B.vers) /\ (G0.c, G0.d) <> (G0.c', G0.d')] 
      = Pr[G0(B(A)).main(h) @ &m : res /\ B.vers /\ (G0.c, G0.d) <> (G0.c', G0.d')].
  rewrite Pr[mu_eq]. auto. auto. auto.
have ->: Pr[G0(B(A)).main(h) @ &m : res /\ B.vers /\ (G0.c, G0.d) <> (G0.c', G0.d')]
 = Pr[G0(B(A)).main(h) @ &m : B.vers /\ (G0.c, G0.d) <> (G0.c', G0.d')].
rewrite step1. auto.
have ->: Pr[G0(B(A)).main(h) @ &m : res /\ B.vers /\ (G0.c, G0.d) = (G0.c', G0.d')] +
Pr[G0(B(A)).main(h) @ &m : B.vers /\ (G0.c, G0.d) <> (G0.c', G0.d')] +
(1%r / 2%r * Pr[G0(B(A)).main(h) @ &m : !B.vers] -
 Pr[G0(B(A)).main(h) @ &m : !B.vers /\ G0.m = G0.m' /\ (G0.c, G0.d) = (G0.c', G0.d')]) -
1%r / 2%r = 
 Pr[G0(B(A)).main(h) @ &m : res /\ B.vers /\ (G0.c, G0.d) = (G0.c', G0.d')] +
Pr[G0(B(A)).main(h) @ &m : B.vers /\ (G0.c, G0.d) <> (G0.c', G0.d')] +
1%r / 2%r * Pr[G0(B(A)).main(h) @ &m : !B.vers] - 1%r / 2%r
- Pr[G0(B(A)).main(h) @ &m : !B.vers /\ G0.m = G0.m' /\ (G0.c, G0.d) = (G0.c', G0.d')].
smt. 
have ->: Pr[G0(B(A)).main(h) @ &m : res /\ B.vers /\ (G0.c, G0.d) = (G0.c', G0.d')] +
Pr[G0(B(A)).main(h) @ &m : B.vers /\ (G0.c, G0.d) <> (G0.c', G0.d')] +
1%r / 2%r * Pr[G0(B(A)).main(h) @ &m : !B.vers] - 1%r / 2%r
 = Pr[G0(B(A)).main(h) @ &m : res /\ B.vers /\ (G0.c, G0.d) = (G0.c', G0.d')] +
Pr[G0(B(A)).main(h) @ &m : B.vers /\ (G0.c, G0.d) <> (G0.c', G0.d')] +
1%r / 2%r * (Pr[G0(B(A)).main(h) @ &m : !B.vers] - 1%r). 
smt.
have ->: (Pr[G0(B(A)).main(h) @ &m : !B.vers] - 1%r)
 =  - Pr[G0(B(A)).main(h) @ &m : B.vers].
rewrite - (ss &m h).
 have : Pr[G0(B(A)).main(h) @ &m : true]
  = Pr[G0(B(A)).main(h) @ &m : B.vers] + Pr[G0(B(A)).main(h) @ &m : !B.vers].
  rewrite Pr[mu_split B.vers]. auto.
smt.
have ->: Pr[G0(B(A)).main(h) @ &m : res /\ B.vers /\ (G0.c, G0.d) = (G0.c', G0.d')] +
Pr[G0(B(A)).main(h) @ &m : B.vers /\ (G0.c, G0.d) <> (G0.c', G0.d')] +
1%r / 2%r * - Pr[G0(B(A)).main(h) @ &m : B.vers]
 = Pr[G0(B(A)).main(h) @ &m : res /\ B.vers /\ (G0.c, G0.d) = (G0.c', G0.d')] +
Pr[G0(B(A)).main(h) @ &m : B.vers /\ (G0.c, G0.d) <> (G0.c', G0.d')] -
1%r / 2%r * Pr[G0(B(A)).main(h) @ &m : B.vers]. smt.
have ->: Pr[G0(B(A)).main(h) @ &m : B.vers]
= Pr[BEP(A).main() @ &m : res].
rewrite (step2 &m h). auto.
have ->: Pr[G0(B(A)).main(h) @ &m : res /\ B.vers /\ (G0.c, G0.d) = (G0.c', G0.d')] = 0%r. 
byphoare. hoare. conseq (_: true ==> res => (G0.c, G0.d) <> (G0.c', G0.d')) . smt.
proc. inline*. wp. rnd. wp.  rnd. rnd. wp.  call (_:true). wp. rnd.
skip. progress. smt. auto.
have f : Pr[G0(B(A)).main(h) @ &m : B.vers /\ (G0.c, G0.d) <> (G0.c', G0.d')]
 <= Pr[BEP(A).main() @ &m : res].
rewrite (step2 &m h). rewrite Pr[mu_sub]. auto. auto.
simplify.
have ff : (Pr[BEP(A).main() @ &m : res] / 2%r -
2%r * Pr[G0(B(A)).main(h) @ &m : B.vers /\ G0.c = G0.c' /\ G0.d = G0.d']) 
 + Pr[G0(B(A)).main(h) @ &m : B.vers /\ G0.c = G0.c' /\ G0.d = G0.d']
  <=
(Pr[G0(B(A)).main(h) @ &m : B.vers /\ ! (G0.c = G0.c' /\ G0.d = G0.d')] -
Pr[BEP(A).main() @ &m : res] / 2%r)
 + Pr[G0(B(A)).main(h) @ &m : B.vers /\ G0.c = G0.c' /\ G0.d = G0.d'].
  have ->: 
  (Pr[G0(B(A)).main(h) @ &m : B.vers /\ ! (G0.c = G0.c' /\ G0.d = G0.d')] -
Pr[BEP(A).main() @ &m : res] / 2%r)
 + Pr[G0(B(A)).main(h) @ &m : B.vers /\ G0.c = G0.c' /\ G0.d = G0.d']
  = Pr[BEP(A).main() @ &m : res] / 2%r.
have : Pr[G0(B(A)).main(h) @ &m : B.vers /\ ! (G0.c = G0.c' /\ G0.d = G0.d')]
 + Pr[G0(B(A)).main(h) @ &m : B.vers /\ (G0.c = G0.c' /\ G0.d = G0.d')]
 = Pr[BEP(A).main() @ &m : res]. rewrite (step2 &m h).
  have ->: Pr[G0(B(A)).main(h) @ &m : B.vers]
  = Pr[G0(B(A)).main(h) @ &m : B.vers /\ ! (G0.c = G0.c' /\ G0.d = G0.d')] +
  Pr[G0(B(A)).main(h) @ &m : B.vers /\ G0.c = G0.c' /\ G0.d = G0.d'].
  rewrite Pr[mu_split (G0.c = G0.c' /\ G0.d = G0.d')]. smt. auto.
smt. smt. smt.
qed.


local lemma G1ub &m h : forall (S <: Simulator),
   Pr[ G1(B(A), S).main(h) @ &m : res ] <= 1%r/2%r.
proof. move => S. byphoare (_: arg = h ==> _).
proc. inline*.
swap 8 1. 
seq 5 : (B.m1 <> B.m2) (1%r/2%r) .
wp. call (_: true). wp. rnd. skip. auto.
simplify. wp. 
conseq (_: true ==> B.m1 <> B.m2). auto.
sp.
conseq (_: _ ==>   m = m'). smt.
rnd. call (_:true). wp. skip. progress.
rewrite duniform1E_uniq. smt. simplify. smt.
wp. hoare.
simplify. call (_:true ==> res.`2 <> res.`4). apply ba.
wp. rnd.  skip. auto. auto. auto. auto.
qed.


require import StdOrder.
import RealOrder.


local lemma bme (c a b : real) : 
 a + c <= b + c => a <= b.
smt. qed.

  
local lemma final_binding &m h :  forall (S <: Simulator {B, A}),
 1%r/2%r * Pr[ BEP(A).main() @ &m : res ]
 - 3%r * Pr[ G0(B(A)).main(h) @ &m : (G0.c,G0.d) = (G0.c',G0.d') ] 
 <= Pr[ SG0(B(A)).main(h) @ &m : res ] - Pr[ SG1(B(A),S).main(h) @ &m : res ].
proof. move => S. 
have ->: Pr[ SG0(B(A)).main(h) @ &m : res ] = Pr[ G0(B(A)).main(h) @ &m : res ].
byequiv. sim. auto. auto.
have ->: Pr[ SG1(B(A),S).main(h) @ &m : res ] = Pr[ G1(B(A),S).main(h) @ &m : res ].
byequiv. sim. auto. auto.
have f1 :  1%r/2%r * Pr[ BEP(A).main() @ &m : res ]
 - 2%r * Pr[ G0(B(A)).main(h) @ &m : B.vers /\ (G0.c,G0.d) = (G0.c',G0.d') ] 
 <= Pr[ G0(B(A)).main(h) @ &m : res ] - 1%r/2%r
 + Pr[ G0(B(A)).main(h) @ &m : !B.vers /\ G0.m = G0.m' /\ (G0.c,G0.d) = (G0.c',G0.d') ]. apply step6.
have f2 : Pr[G0(B(A)).main(h) @ &m : B.vers /\ (G0.c, G0.d) = (G0.c', G0.d')]
 <= Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')].
rewrite Pr[mu_sub]. auto. auto.
have f3 :  1%r/2%r * Pr[ BEP(A).main() @ &m : res ]
 - 2%r * Pr[ G0(B(A)).main(h) @ &m : (G0.c,G0.d) = (G0.c',G0.d') ] 
 <= 1%r/2%r * Pr[ BEP(A).main() @ &m : res ]
 - 2%r * Pr[ G0(B(A)).main(h) @ &m : B.vers /\ (G0.c,G0.d) = (G0.c',G0.d') ].
smt. clear f2.
have f4 : 1%r / 2%r * Pr[BEP(A).main() @ &m : res]
            - 2%r * Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')] <=
    Pr[G0(B(A)).main(h) @ &m : res] - 1%r / 2%r +
    Pr[G0(B(A)).main(h) @ &m :
       !B.vers /\ G0.m = G0.m' /\ (G0.c, G0.d) = (G0.c', G0.d')].
apply (ler_trans (1%r/2%r * Pr[ BEP(A).main() @ &m : res ]
 - 2%r * Pr[ G0(B(A)).main(h) @ &m : B.vers /\ (G0.c,G0.d) = (G0.c',G0.d') ]) 
      (1%r / 2%r * Pr[BEP(A).main() @ &m : res]
         - 2%r * Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')]) ). 
auto. auto. clear f3 f1.
have f5 : Pr[G0(B(A)).main(h) @ &m :
       !B.vers /\ G0.m = G0.m' /\ (G0.c, G0.d) = (G0.c', G0.d')]
 <= Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')].
rewrite Pr[mu_sub]. auto. auto.
have f6 : Pr[G0(B(A)).main(h) @ &m : res] - 1%r / 2%r +
    Pr[G0(B(A)).main(h) @ &m :
       !B.vers /\ G0.m = G0.m' /\ (G0.c, G0.d) = (G0.c', G0.d')]
 <= Pr[G0(B(A)).main(h) @ &m : res] - 1%r / 2%r +
    Pr[G0(B(A)).main(h) @ &m :
       !B.vers /\ G0.m = G0.m' /\ (G0.c, G0.d) = (G0.c', G0.d')].
smt. clear f5. 
have f7 : 1%r / 2%r * Pr[BEP(A).main() @ &m : res] -
    2%r * Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')] <=
    Pr[G0(B(A)).main(h) @ &m : res] - 1%r / 2%r +
    Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')].
apply (ler_trans (
    Pr[G0(B(A)).main(h) @ &m : res] - 1%r / 2%r +
    Pr[G0(B(A)).main(h) @ &m :
       !B.vers /\ G0.m = G0.m' /\ (G0.c, G0.d) = (G0.c', G0.d')]) ).
auto. smt. clear f6 f4.
have f4 : Pr[ G1(B(A), S).main(h) @ &m : res ] <= 1%r/2%r.
apply (G1ub &m h S).
have f9 : 
  Pr[G0(B(A)).main(h) @ &m : res] - 1%r / 2%r
 <= Pr[G0(B(A)).main(h) @ &m : res] - Pr[G1(B(A), S).main(h) @ &m : res].
smt.
apply (ler_trans (Pr[G0(B(A)).main(h) @ &m : res] - 1%r/2%r) ).
clear f4.
have ->: 1%r / 2%r * Pr[BEP(A).main() @ &m : res] -
3%r * Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')]
 = 1%r / 2%r * Pr[BEP(A).main() @ &m : res] - 2%r * Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')]
 - Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')].
smt. apply (bme (Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')])).
have ->:
 1%r / 2%r * Pr[BEP(A).main() @ &m : res] -
2%r * Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')] -
Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')] +
Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')] 
 = 1%r / 2%r * Pr[BEP(A).main() @ &m : res] -
2%r * Pr[G0(B(A)).main(h) @ &m : (G0.c, G0.d) = (G0.c', G0.d')].
smt. apply f7. smt.
qed.


local lemma nsnm_pure_binding' &m h :  forall (S <: Simulator {B, A}),
  Pr[ BindingExperiment(A).main() @ &m : res ] <= 
  2%r * (Pr[ SG0(B(A)).main(h) @ &m : res ] - Pr[ SG1(B(A),S).main(h) @ &m : res ]) 
   + 6%r * Pr[ G0(B(A)).main(h) @ &m : (G0.c,G0.d) = (G0.c',G0.d') ].
move => S.
have ->:   Pr[ BindingExperiment(A).main() @ &m : res ] = Pr[ BEP(A).main() @ &m : res ]. 
byequiv. sim. auto. auto.
have :  1%r/2%r * Pr[ BEP(A).main() @ &m : res ]
 - 3%r * Pr[ G0(B(A)).main(h) @ &m : (G0.c,G0.d) = (G0.c',G0.d') ] 
 <= Pr[ SG0(B(A)).main(h) @ &m : res ] - Pr[ SG1(B(A),S).main(h) @ &m : res ].
apply (final_binding &m h S). 
smt.
qed.


local lemma guessprob &m h : 
  Pr[ G0(B(A)).main(h) @ &m : (G0.c,G0.d) = (G0.c',G0.d') ]
  <=   Pr[ UnpredGame(BG(A)).main() @ &m : res ].
proof. byequiv.
proc. inline*. swap {1} [14..15] -5.
wp. rnd.  wp. rnd. wp. rnd.  wp.  call (_:true).
wp.   rnd. 
skip. progress.  smt.
auto. auto.
qed.


(* novel simulation-based non-malleability implies binding *)
lemma nsnm_pure_binding &m h :  forall (S <: Simulator {B, A}),
  Pr[ BindingExperiment(A).main() @ &m : res ] <= 
  2%r * (Pr[ SG0(B(A)).main(h) @ &m : res ] - Pr[ SG1(B(A),S).main(h) @ &m : res ]) 
   + 6%r * Pr[ UnpredGame(BG(A)).main() @ &m : res ].
proof.  move => S.
have f :   Pr[ BindingExperiment(A).main() @ &m : res ] <= 
  2%r * (Pr[ SG0(B(A)).main(h) @ &m : res ] - Pr[ SG1(B(A),S).main(h) @ &m : res ]) 
   + 6%r * Pr[ G0(B(A)).main(h) @ &m : (G0.c,G0.d) = (G0.c',G0.d') ].
apply (nsnm_pure_binding' &m h S).
smt.
qed.

end section.




end NSNM_binding_theory.
