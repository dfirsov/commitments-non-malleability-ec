pragma Goals:printall.
require import DBool List Real.
require import Commitment.
require import Distr AllCore.


require import D1D2.
require import NSNM_Definition.
require import NSNM_Pure_Hiding.

require CommitmentUnpredictability.

clone import CommitmentProtocol as CP with type value      <- value,
                                           type message    <- message,
                                           type commitment <- commitment,
                                           type openingkey <- openingkey.

clone import NSNM_hiding_theory as HE. 
import HE.CU.                  

op diff : value -> message -> message.
axiom diff_correct (pk : value) (m : message) : m <> diff pk m.


module U'(U : Unhider) : Unhider = {
 var m1,m2 : message  
  proc choose(x : value) : message * message = {    
    var pk;
    pk <- x;
    (m1, m2) <@ U.choose(pk);
    return (m1, (if (m1 = m2) then diff pk m2 else m2)); 
  }

  proc guess(z : commitment) : bool = {
    var bb, b';
    b' <- U.guess(z);
    bb <$ {0,1};
    return (if (m1 = m2) then bb else b');
  }
}.

section.


declare module A : Unhider {HEPT0, HEPT1, HEP, U', H}.
axiom Ag_ll : islossless A.guess.
axiom Ac_ll : islossless A.choose.

lemma Ag_ll1 : phoare[ U'(A).guess : true ==> true] = 1%r. 
proof.
proc. rnd. call(_:true). apply Ag_ll. skip. progress. smt.  
qed.

lemma Ac_ll1 : phoare[ U'(A).choose : true ==> true] = 1%r. 
proof.
proc. call(_:true). apply Ac_ll. wp. skip. progress.
qed.

lemma hh0 : phoare [ U'(A).choose : true ==> res.`1 <> res.`2 ] = 1%r.
proof.  
proc. call(_:true). 
apply Ac_ll. wp. skip. progress. smt. 
qed.

local lemma h1 &m:
  Pr[ HEPT0(U'(A)).main() @ &m : HEP.m1 <> HEP.m2 ] = 1%r.
proof. 
byphoare =>//. proc. inline*. wp. rnd. call(_:true). 
apply Ag_ll. wp. rnd. wp. call(_:true). apply Ac_ll. 
wp. rnd. skip. progress.   
have ->: (mu Dpk
  (fun (x : value) =>
     forall (result : message * message),
       (result.`1 <>
        (if result.`1 = result.`2 then diff x result.`2 else result.`2) /\
        weight {0,1} = 1%r) /\
       weight (Com x result.`1) = 1%r) =
1%r) = (mu Dpk
  (fun (x : value) =>
     forall (result : message * message),
       (result.`1 <>
        (if result.`1 = result.`2 then diff x result.`2 else result.`2) /\
        true) /\ true) =
1%r). smt. progress.
smt. 
qed.

local lemma h2 &m:
  Pr[ HEPT1(U'(A)).main() @ &m : HEP.m1 <> HEP.m2 ] = 1%r.
proof. 
byphoare =>//. proc. inline*. wp. rnd. call(_:true). 
apply Ag_ll. wp. rnd. wp. call(_:true). apply Ac_ll. 
wp. rnd. skip. progress.
have ->: (mu Dpk
  (fun (x : value) =>
     forall (result : message * message),
       (result.`1 <>
        (if result.`1 = result.`2 then diff x result.`2 else result.`2) /\
        weight {0,1} = 1%r) /\
       weight
         (Com x
           (if result.`1 = result.`2 then diff x result.`2 else result.`2)) = 1%r) = 1%r) =
(mu Dpk  (fun (x : value) => forall (result : message * message),
       (result.`1 <> (if result.`1 = result.`2 then diff x result.`2 else result.`2) /\
        true) /\ true) =
1%r). smt. smt. 
qed.

(* HEPT0 and HEPT1 equal when m1 = m2 *)
local lemma eq1 &m:
   Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ] <=
   Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ].
proof.
byequiv =>//. proc.
seq 2 2 : (={glob A, HEP.m1, HEP.m2} /\ HEPT0.x{1} = HEPT1.x{2}). 
call(_:true). rnd. skip. progress. 
case (HEP.m1{1} = HEP.m2{2}).
call(_:true). rnd. 
skip. progress. 

call{1} Ag_ll. call{2} Ag_ll. rnd{1}. rnd{2}.  
skip. progress. 
smt. smt. smt.  
qed.


local lemma eq2 &m:
  Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ] <=
  Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ].
proof.
byequiv=>//. proc. symmetry.   
seq 2 2 : (={glob A, HEP.m1, HEP.m2} /\ HEPT0.x{1} = HEPT1.x{2}). 
call(_:true). rnd. skip. progress. 
case (HEP.m1{1} = HEP.m2{2}).
call(_:true). rnd. 
skip. progress. 

call{1} Ag_ll. call{2} Ag_ll. rnd{1}. rnd{2}.  
skip. progress. 
smt. smt. smt.  
qed.


local lemma eq &m:
   Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ] =
   Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ].
proof.
have : Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ] <=
   Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ]. apply eq1. progress.
have : Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ] <=
  Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ]. apply eq2. progress.
smt. 
qed.   

(* HEP.m1 HEP.m2 - U'.m1 U'.m2 *)

local lemma f1 &m:
  Pr[ HEPT0(U'(A)).main() @ &m : U'.m1 = U'.m2 ] = Pr[ HEPT1(U'(A)).main() @ &m : U'.m1 = U'.m2 ].
proof. 
byequiv =>//. proc. inline*.
wp. rnd. call {1} Ag_ll. call {2} Ag_ll. 
wp. rnd{1}. rnd{2}.  wp. call (_:true). wp. rnd.
skip. progress. smt. smt. 
qed.

local lemma f2 &m:
  Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ] <= Pr[ HEPT1(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ].
proof. 
byequiv =>//.
proc. inline*.
wp. rnd{2}. sp.
seq 2 5 : (HEP.m1{1} <> HEP.m2{1} => ={glob A, HEP.m1, HEP.m2, HEPT1.x} /\ U'.m1{2} = HEP.m1{1} /\ U'.m2{2} = HEP.m2{1}).
wp. call (_:true). wp.  rnd.
skip. progress.  smt.      

case (HEP.m1{1} <> HEP.m2{1}).
call (_:true). wp. rnd.  
skip. progress. smt. smt. smt. smt. smt. 
simplify. 
call{1} Ag_ll. call{2} Ag_ll. wp. rnd{1}. rnd{2}.   
skip. progress. smt. smt. 
qed.


local lemma f3 &m:
  Pr[ HEPT1(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ] <= Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ].
proof. 
byequiv =>//.
proc. inline*.
wp. rnd{1}. sp.
seq 5 2 : ( U'.m1{1} <> U'.m2{1} => ={glob A, HEP.m1, HEP.m2, HEPT1.x} /\ U'.m1{1} = HEP.m1{2} /\ U'.m2{1} = HEP.m2{2}).
wp. call (_:true). wp. rnd.
skip. progress.  smt.      

case (U'.m1{1} <> U'.m2{1}).
call (_:true). wp. rnd.  
skip. progress. smt. smt. smt. smt. smt. 
simplify. 
call{1} Ag_ll. call{2} Ag_ll. wp. rnd{1}. rnd{2}.   
skip. progress. smt. smt. 
qed.



local lemma f4 &m:
  Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ] = Pr[ HEPT1(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ].
proof. 
have a1 : Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ] <= Pr[ HEPT1(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ]. apply f2. progress.
have a2 : Pr[ HEPT1(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ] <= Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ]. apply f3. progress.
smt.
qed. 


local lemma k2 &m:
  Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ] <= Pr[ HEPT0(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ].
proof. 
byequiv =>//.
proc. inline*. wp. rnd{2}. 
seq 2 5 : (HEP.m1{1} <> HEP.m2{1} => ={glob A, HEP.m1, HEP.m2, HEPT0.x} /\ U'.m1{2} = HEP.m1{1} /\ U'.m2{2} = HEP.m2{1}).
wp. call (_:true). wp.  rnd.
skip. progress.  smt.  

case (HEP.m1{1} <> HEP.m2{1}).
call(_:true). wp.  rnd. 
skip. progress.  smt. smt. smt. smt. smt. 

simplify. 
call{1} Ag_ll. call{2} Ag_ll. wp. rnd{1}. rnd{2}.   
skip. progress. smt. smt. 
qed.


local lemma k3 &m:
  Pr[ HEPT0(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ] <= Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ].
proof. 
byequiv =>//.
proc. inline*. wp. rnd{1}. 
seq 5 2 : ( U'.m1{1} <> U'.m2{1} => ={glob A, HEP.m1, HEP.m2, HEPT0.x} /\ U'.m1{1} = HEP.m1{2} /\ U'.m2{1} = HEP.m2{2}).
wp. call (_:true). wp. rnd.
skip. progress.  smt.      

case (U'.m1{1} <> U'.m2{1}).
call (_:true). wp. rnd.  
skip. progress. smt. smt. smt. smt. smt. 
simplify. 
call{1} Ag_ll. call{2} Ag_ll. wp. rnd{1}. rnd{2}.   
skip. progress. smt. smt. 
qed.


local lemma k4 &m:
  Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ] = Pr[ HEPT0(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ].
proof. 
have a1 : Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ] <= Pr[ HEPT0(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ]. apply k2. progress.
have a2 : Pr[ HEPT0(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ] <= Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ]. apply k3. progress.
smt.
qed. 


local lemma k5 &m:
  Pr[ HEPT0(U'(A)).main() @ &m : res /\ U'.m1 = U'.m2 ] = Pr[ HEPT1(U'(A)).main() @ &m : res /\ U'.m1 = U'.m2 ].
proof.
have a1 : Pr[ HEPT0(U'(A)).main() @ &m : res /\ U'.m1 = U'.m2 ] >= Pr[ HEPT1(U'(A)).main() @ &m : res /\ U'.m1 = U'.m2 ].
byequiv =>//.
proc. inline*.
wp. rnd. call {1} Ag_ll. 
call {2} Ag_ll. 
wp.  rnd{1}. rnd{2}. wp. call (_:true). wp. rnd.
skip. progress. smt.  smt. smt.  smt. 
have a2 : Pr[ HEPT1(U'(A)).main() @ &m : res /\ U'.m1 = U'.m2 ] >= Pr[ HEPT0(U'(A)).main() @ &m : res /\ U'.m1 = U'.m2 ].
byequiv =>//.
proc. inline*.
wp. rnd. call {1} Ag_ll. 
call {2} Ag_ll.  
wp.  rnd{1}. rnd{2}.  wp. call (_:true). wp. rnd.
skip. progress. smt. smt.  smt. 
smt. smt. 
qed.


local lemma fin &m:
  (Pr[ HEPT1(A).main() @ &m : res ] - Pr[ HEPT0(A).main() @ &m : res ]) <=
  (Pr[ HEPT1(U'(A)).main() @ &m : res ] - Pr[ HEPT0(U'(A)).main() @ &m : res ]).
proof.
have ->: Pr[ HEPT0(A).main() @ &m : res ] = Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ]
 + Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ].
rewrite Pr[mu_split HEP.m1 = HEP.m2]. auto.
have ->: Pr[ HEPT1(A).main() @ &m : res ] = Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ]
 + Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ].
rewrite Pr[mu_split HEP.m1 = HEP.m2]. auto.
have ->: Pr[ HEPT0(U'(A)).main() @ &m : res ] = Pr[ HEPT0(U'(A)).main() @ &m : res /\ U'.m1 = U'.m2 ]
 + Pr[ HEPT0(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ].
rewrite Pr[mu_split U'.m1 = U'.m2]. auto.
have ->: Pr[ HEPT1(U'(A)).main() @ &m : res ] = Pr[ HEPT1(U'(A)).main() @ &m : res /\ U'.m1 = U'.m2 ]
 + Pr[ HEPT1(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ].
rewrite Pr[mu_split U'.m1 = U'.m2]. auto.
 
have f1 : Pr[ HEPT0(U'(A)).main() @ &m : res /\ U'.m1 = U'.m2 ] = Pr[ HEPT1(U'(A)).main() @ &m : res /\ U'.m1 = U'.m2 ].
apply k5. rewrite f1. smt.
qed.


local lemma h3 &m:
  (Pr[ HidingExperiment1(A).main() @ &m : res ] - Pr[ HidingExperiment0(A).main() @ &m : res ]) <=
  (Pr[ HidingExperiment1(U'(A)).main() @ &m : res ] - Pr[ HidingExperiment0(U'(A)).main() @ &m : res ]).
proof.
have ->: (Pr[ HidingExperiment1(A).main() @ &m : res ]) = (Pr[ HEPT1(A).main() @ &m : res ]).
byequiv =>//. sim. 
have ->: (Pr[ HidingExperiment0(A).main() @ &m : res ]) = (Pr[ HEPT0(A).main() @ &m : res ]).
byequiv =>//. sim. 
have ->: (Pr[ HidingExperiment1(U'(A)).main() @ &m : res ]) = (Pr[ HEPT1(U'(A)).main() @ &m : res ]).
byequiv =>//. sim.
have ->: (Pr[ HidingExperiment0(U'(A)).main() @ &m : res ]) = (Pr[ HEPT0(U'(A)).main() @ &m : res ]).
byequiv =>//. sim. 
apply fin.
qed.

local lemma fin1 &m:
  (Pr[ HEPT0(A).main() @ &m : res ] - Pr[ HEPT1(A).main() @ &m : res ]) <=
  (Pr[ HEPT0(U'(A)).main() @ &m : res ] - Pr[ HEPT1(U'(A)).main() @ &m : res ]).
proof.
have ->: Pr[ HEPT0(A).main() @ &m : res ] = Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ]
 + Pr[ HEPT0(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ].
rewrite Pr[mu_split HEP.m1 = HEP.m2]. auto.
have ->: Pr[ HEPT1(A).main() @ &m : res ] = Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 = HEP.m2 ]
 + Pr[ HEPT1(A).main() @ &m : res /\ HEP.m1 <> HEP.m2 ].
rewrite Pr[mu_split HEP.m1 = HEP.m2]. auto.
have ->: Pr[ HEPT0(U'(A)).main() @ &m : res ] = Pr[ HEPT0(U'(A)).main() @ &m : res /\ U'.m1 = U'.m2 ]
 + Pr[ HEPT0(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ].
rewrite Pr[mu_split U'.m1 = U'.m2]. auto.
have ->: Pr[ HEPT1(U'(A)).main() @ &m : res ] = Pr[ HEPT1(U'(A)).main() @ &m : res /\ U'.m1 = U'.m2 ]
 + Pr[ HEPT1(U'(A)).main() @ &m : res /\ U'.m1 <> U'.m2 ].
rewrite Pr[mu_split U'.m1 = U'.m2]. auto.
smt. 
qed.


local lemma h4 &m:
  (Pr[ HidingExperiment0(A).main() @ &m : res ] - Pr[ HidingExperiment1(A).main() @ &m : res ]) <=
  (Pr[ HidingExperiment0(U'(A)).main() @ &m : res ] - Pr[ HidingExperiment1(U'(A)).main() @ &m : res ]).
proof.
have ->: (Pr[ HidingExperiment1(A).main() @ &m : res ]) = (Pr[ HEPT1(A).main() @ &m : res ]).
byequiv =>//. sim. 
have ->: (Pr[ HidingExperiment0(A).main() @ &m : res ]) = (Pr[ HEPT0(A).main() @ &m : res ]).
byequiv =>//. sim. 
have ->: (Pr[ HidingExperiment1(U'(A)).main() @ &m : res ]) = (Pr[ HEPT1(U'(A)).main() @ &m : res ]).
byequiv =>//. sim.
have ->: (Pr[ HidingExperiment0(U'(A)).main() @ &m : res ]) = (Pr[ HEPT0(U'(A)).main() @ &m : res ]).
byequiv =>//. sim. smt. 
qed.

local lemma snnm_pure_hiding2 &m h : forall (S <: Simulator {H, A, U'}),
 (Pr[ HidingExperiment1(U'(A)).main() @ &m : res ] - Pr[ HidingExperiment0(U'(A)).main() @ &m : res ]) 
 <= 2%r * (Pr[ SG0(H(U'(A))).main(h) @ &m : res ] - Pr[ SG1(H(U'(A)),S).main(h) @ &m : res ]
 + Pr[ UnpredGame(HU(U'(A))).main() @ &m : res ]).
proof. 
apply (snnm_pure_hiding1 (U'(A)) Ag_ll1 Ac_ll1 h1 h2 hh0 &m h).
qed.


(* final 1 *)
local lemma snnm_pure_hiding_f &m h : forall (S <: Simulator {H, A, U'}),
 (Pr[ HidingExperiment1(A).main() @ &m : res ] - Pr[ HidingExperiment0(A).main() @ &m : res ]) 
 <= 2%r * (Pr[ SG0(H(U'(A))).main(h) @ &m : res ] - Pr[ SG1(H(U'(A)),S).main(h) @ &m : res ]
 + Pr[ UnpredGame(HU(U'(A))).main() @ &m : res ]).
proof. progress. 
have :  (Pr[ HidingExperiment1(U'(A)).main() @ &m : res ] - Pr[ HidingExperiment0(U'(A)).main() @ &m : res ]) 
 <= 2%r * (Pr[ SG0(H(U'(A))).main(h) @ &m : res ] - Pr[ SG1(H(U'(A)),S).main(h) @ &m : res ]
 + Pr[ UnpredGame(HU(U'(A))).main() @ &m : res ]).
apply (snnm_pure_hiding1 (U'(A)) Ag_ll1 Ac_ll1 h1 h2 hh0 &m h S). progress.
have : (Pr[ HidingExperiment1(A).main() @ &m : res ] - Pr[ HidingExperiment0(A).main() @ &m : res ]) <=
(Pr[ HidingExperiment1(U'(A)).main() @ &m : res ] - Pr[ HidingExperiment0(U'(A)).main() @ &m : res ]).
smt. progress. smt.  
qed.


local lemma ul1 &m : Pr[ HidingExperiment0(F(U'(A))).main() @ &m : res ] = Pr[ HidingExperiment0(U'(A)).main() @ &m : !res ].
proof. byequiv =>//. proc. inline*. wp. rnd. call (_:true).
wp.  rnd. wp.  call (_:true). wp. rnd. skip. progress. 
qed.

local lemma ul11 &m : Pr[ HidingExperiment0(F(U'(A))).main() @ &m : res ] = 1%r - Pr[ HidingExperiment0(U'(A)).main() @ &m : res ].
proof. rewrite ul1 Pr[mu_not]. 
have ->: Pr[HidingExperiment0(U'(A)).main() @ &m : true] = 1%r.
byphoare =>//. proc. call Ag_ll1. wp.  rnd.  call Ac_ll1. rnd. skip.  smt. auto.
qed.

local lemma ul2 &m : Pr[ HidingExperiment1(F(U'(A))).main() @ &m : res ] = Pr[ HidingExperiment1(U'(A)).main() @ &m : !res ].
proof. byequiv =>//. proc. inline*. wp. rnd. call (_:true).
wp.  rnd. wp.  call (_:true). wp. rnd. skip. progress. 
qed.

local lemma ul22 &m : Pr[ HidingExperiment1(F(U'(A))).main() @ &m : res ] = 1%r - Pr[ HidingExperiment1(U'(A)).main() @ &m : res ].
proof. rewrite ul2 Pr[mu_not]. 
have ->: Pr[HidingExperiment1(U'(A)).main() @ &m : true] = 1%r.
byphoare =>//. proc. call Ag_ll1. wp.  rnd.  call Ac_ll1. rnd. skip.  smt. auto. 
qed.

local lemma ul3 &m : Pr[ HidingExperiment1(F(U'(A))).main() @ &m : res ] 
 - Pr[ HidingExperiment0(F(U'(A))).main() @ &m : res ] = - (Pr[ HidingExperiment1(U'(A)).main() @ &m : res ] - 
  Pr[ HidingExperiment0(U'(A)).main() @ &m : res ] ).
proof. smt.
qed.

local lemma snnm_pure_hiding3 &m h : forall (S <: Simulator {H, A, U'}),
 (Pr[ HidingExperiment1(F(U'(A))).main() @ &m : res ] - Pr[ HidingExperiment0(F(U'(A))).main() @ &m : res ]) 
 <= 2%r * (Pr[ SG0(H(F(U'(A)))).main(h) @ &m : res ] - Pr[ SG1(H(F(U'(A))),S).main(h) @ &m : res ]
 + Pr[ UnpredGame(HU(F(U'(A)))).main() @ &m : res ]).
proof. move => S.  
have a1 : phoare[ F(U'(A)).guess : true ==> true] = 1%r. 
proc. call Ag_ll1. auto.
have a2:  phoare[ F(U'(A)).choose : true ==> true] = 1%r. 
proc. call Ac_ll1. auto.
have a3 : forall &m, Pr[HEPT0(F(U'(A))).main() @ &m : HEP.m1 <> HEP.m2] = 1%r. 
move => &m0.
have ->: Pr[HEPT0(F(U'(A))).main() @ &m0 : HEP.m1 <> HEP.m2] = Pr[HEPT0(U'(A)).main() @ &m0 : HEP.m1 <> HEP.m2].
byequiv =>//. proc.  inline*. wp. rnd. call (_:true). wp. rnd.  wp. call (_:true). wp. rnd. skip. progress. apply h1.
have a4 : forall &m, Pr[HEPT1(F(U'(A))).main() @ &m : HEP.m1 <> HEP.m2] = 1%r. move => &m0.
have ->: Pr[HEPT1(F(U'(A))).main() @ &m0 : HEP.m1 <> HEP.m2] = Pr[HEPT1(U'(A)).main() @ &m0 : HEP.m1 <> HEP.m2].
byequiv =>//. proc.  inline*. wp. rnd. call (_:true). wp. rnd.  wp. call (_:true). wp. rnd. skip. progress. apply h2.
have a5:  phoare[ F(U'(A)).choose : true ==> res.`1 <> res.`2] = 1%r. 
proc. call hh0. skip. auto.
apply (snnm_pure_hiding1 (F(U'(A))) a1 a2 a3 a4 a5 &m h S).     
qed.


local lemma nsnm_pure_hiding_f' &m h : forall (S <: Simulator {H, A, U'}),
 `|Pr[ HidingExperiment1(U'(A)).main() @ &m : res ] - Pr[ HidingExperiment0(U'(A)).main() @ &m : res ]|
 <= maxr
      (2%r * (Pr[ SG0(H(F(U'(A)))).main(h) @ &m : res ] - Pr[ SG1(H(F(U'(A))),S).main(h) @ &m : res ]
        + Pr[ UnpredGame(HU(F(U'(A)))).main() @ &m : res ]))
      (2%r * (Pr[ SG0(H(U'(A))).main(h) @ &m : res ] - Pr[ SG1(H(U'(A)),S).main(h) @ &m : res ]
        + Pr[ UnpredGame(HU(U'(A))).main() @ &m : res ])).
proof. progress. 
apply (nsnm_pure_hiding_final (U'(A)) Ag_ll1 Ac_ll1 h1 h2 hh0 &m h S).
qed.


(* final 2 *)
lemma nsnm_pure_hiding_final2 &m h : forall (S <: Simulator {H, A, U'}),
 `|Pr[ HidingExperiment1(A).main() @ &m : res ] - Pr[ HidingExperiment0(A).main() @ &m : res ]|
 <= maxr
      (2%r * (Pr[ SG0(H(F(U'(A)))).main(h) @ &m : res ] - Pr[ SG1(H(F(U'(A))),S).main(h) @ &m : res ]
        + Pr[ UnpredGame(HU(F(U'(A)))).main() @ &m : res ]))
      (2%r * (Pr[ SG0(H(U'(A))).main(h) @ &m : res ] - Pr[ SG1(H(U'(A)),S).main(h) @ &m : res ]
        + Pr[ UnpredGame(HU(U'(A))).main() @ &m : res ])).
proof. progress.
have a1 : (Pr[ HidingExperiment1(U'(A)).main() @ &m : res ] - Pr[ HidingExperiment0(U'(A)).main() @ &m : res ]) 
 <= 2%r * (Pr[ SG0(H(U'(A))).main(h) @ &m : res ] - Pr[ SG1(H(U'(A)),S).main(h) @ &m : res ]
 + Pr[ UnpredGame(HU(U'(A))).main() @ &m : res ]).
  apply (snnm_pure_hiding1 (U'(A)) Ag_ll1 Ac_ll1 h1 h2 hh0 &m h S).     
have a2 : (Pr[ HidingExperiment1(F(U'(A))).main() @ &m : res ] - Pr[ HidingExperiment0(F(U'(A))).main() @ &m : res ]) 
 <= 2%r * (Pr[ SG0(H(F(U'(A)))).main(h) @ &m : res ] - Pr[ SG1(H(F(U'(A))),S).main(h) @ &m : res ]
 + Pr[ UnpredGame(HU(F(U'(A)))).main() @ &m : res ]). apply (snnm_pure_hiding3 &m h S).  
have h3 : (Pr[ HidingExperiment1(A).main() @ &m : res ] - Pr[ HidingExperiment0(A).main() @ &m : res ]) <=
  (Pr[ HidingExperiment1(U'(A)).main() @ &m : res ] - Pr[ HidingExperiment0(U'(A)).main() @ &m : res ]). apply h3. 
have h4 :  (Pr[ HidingExperiment0(A).main() @ &m : res ] - Pr[ HidingExperiment1(A).main() @ &m : res ]) <=
  (Pr[ HidingExperiment0(U'(A)).main() @ &m : res ] - Pr[ HidingExperiment1(U'(A)).main() @ &m : res ]). apply h4.
smt. 
qed.


end section.
 
