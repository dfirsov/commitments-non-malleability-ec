pragma Goals:printall. 

require import AllCore DBool List Distr Real Int. 
require import Commitment.
require WholeMsg D1D2.

theory NM.

type value,  message,  commitment, randomness, openingkey.
type relation = message -> message list -> bool.

clone import CommitmentProtocol as CP with type value      <- value,
                                           type message    <- message,
                                           type commitment <- commitment,
                                           type openingkey <- openingkey.

op Dpk : value distr.
op Dr : randomness distr.
op Com (pk : value) (r : randomness) (m : message) : commitment * openingkey.
op Ver : value -> message * (commitment * openingkey) -> bool.
op mdistr : message distr.

abbrev (\notin) ['a] (z : 'a) (s : 'a list) : bool = !mem s z.

axiom S_correct pk r : pk \in Dpk => forall m, Ver pk (m, (Com pk r m)).
axiom S_inj pk r m1 m2: pk \in Dpk => m1 <> m2 => Ver pk (m1, (Com pk r m2)) = false.

axiom Dpk_ll : is_lossless Dpk.
axiom Dr_ll : is_lossless Dr.
axiom mdistr_ll : is_lossless mdistr.

op FaultyO (c : commitment) (pk : value) : openingkey.
op FaultyM (c : commitment) (pk : value) : message.

axiom F_correct c pk : 
       pk \in Dpk => !Ver pk ((FaultyM c pk), (c, (FaultyO c pk))).


module type AdvNNMO = {
  proc init(pk : value) : message distr
  proc commit(c : commitment) : relation * commitment list
  proc decommit(d : openingkey) : openingkey list * message list
}.


module NNMO_G0(A : AdvNNMO) = {
  var m : message
  var c : commitment

  proc main() : bool = {
    var rel, pk, mdistr, r, d, cs, ds, ms;    
    pk                 <$ Dpk;  
    mdistr             <- A.init(pk);
    m                  <$ mdistr;
    r                  <$ Dr;
    (c, d)             <- Com pk r m;
    (rel, cs)          <- A.commit(c);
    (ds, ms)           <- A.decommit(d);    
    return (forall x, x \in zip ms (zip cs ds) => Ver pk x)  
           /\ rel m ms
           /\ c \notin cs
           /\ size cs = size ds
           /\ size ms = size ds
           /\ cs <> [];
  }
}.


module NNMO_G1(A : AdvNNMO) = {
  var m : message
  var n : message
  var c : commitment
  
  proc main() : bool = {
    var rel, pk, mdistr, r, d, cs, ds, ms;    
    pk                 <$ Dpk;                    
    mdistr             <- A.init(pk);
    m                  <$ mdistr;
    n                  <$ mdistr;  
    r                  <$ Dr;     
    (c, d)             <- Com pk r m;
    (rel, cs)          <- A.commit(c);
    (ds, ms)           <- A.decommit(d);    
    return (forall x, x \in zip ms (zip cs ds) => Ver pk x)
           /\ rel n ms
           /\ c \notin cs
           /\ size cs = size ds
           /\ size ms = size ds
           /\ cs <> [];
  }
}.


end NM.

theory CounterExample2.

type value,  message,  commitment, openingkey.

clone import NM  with type value <- value,
                      type message <- message,
                      type commitment <- commitment,
                      type openingkey <- openingkey.

import NM.CP.

op m1, m2 : message.

axiom m1_and_m2_diff : m1 <> m2.

clone import WholeMsg with type message <- message,
                           type ain <- unit,
                           op m1 <- m1,
                           op m2 <- m2.

module A : AdvNNMO = {

  var pk : value
  var c, c' : commitment
  var d' : openingkey

  proc init(x : value) : message distr = {
    pk <- x;
    return duniform [m1 ; m2];
  }   

  proc commit(y : commitment) : relation * commitment list = {
    var rr, rel;
    
    c <- y;
    rr <$ Dr;
    (c', d') <- Com pk rr m1;    
    rel <- fun (x : message) (xs : message list)
                     => x = m1 /\ head witness xs = m1;
    return (rel, [c']);
  }

  proc decommit(d : openingkey) : openingkey list * message list = {
    return (if Ver pk (m1, (c, d))
                 then ([d'], [m1])
                 else ([(FaultyO c' pk)], [(FaultyM c' pk)]));  
  } 

}.

section.

local lemma g0 &m : Pr[ NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 ] = 1%r/2%r.
proof.
byphoare (_: _ ==> _) => //. 
proc. inline*.
seq 5 : (NNMO_G0.m = m1) (1%r/2%r) (1%r) (1%r/2%r) (0%r).
rnd. wp. rnd. skip. progress. 
rnd. wp. rnd. skip. progress.
rewrite duniformE => //=. case (m1 = m2) => b => //. 
have : m1 <> m2. apply m1_and_m2_diff. 
move => c => //=. rewrite b2i1 => //=. 
rewrite eq_sym in b. rewrite b. rewrite b2i0 => //.  
rewrite Dpk_ll => //.
wp. rnd. wp. rnd. skip. progress. 
rewrite Dr_ll => //. rewrite Dr_ll => //.  
wp. rnd. wp. rnd. skip. progress. 
rewrite H => //. 
rewrite mu0_false. 
progress. auto.    
rewrite Dr_ll => //. 
progress.
qed.    


local lemma g0a &m : Pr[ NNMO_G0(A).main() @ &m : res ] = 1%r/2%r -  
  Pr[ NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c = A.c'].
proof.
have :  Pr[ NNMO_G0(A).main() @ &m : res ] = 
Pr[ NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c <> A.c']. 
byequiv(_: _ ==> _) => //. proc. inline*.
wp.  rnd.  wp.  rnd.  rnd.  wp.  rnd. simplify.
skip. progress.   
have :  Ver pkL (m1, ((Com pkL rL m1).`1, (Com pkL rL m1).`2)). 
have ->: ((Com pkL rL m1).`1, (Com pkL rL m1).`2) = Com pkL rL m1. 
rewrite -pairS => //.
rewrite S_correct. apply H. 
move => h. 
have : x \in
    zip
      (if Ver pkL (m1, ((Com pkL rL m1).`1, (Com pkL rL m1).`2)) 
       then ([(Com pkL rrL m1).`2], [m1])
       else ([FaultyO (Com pkL rrL m1).`1 pkL], [FaultyM (Com pkL rrL m1).`1 pkL])).`2
      (zip [(Com pkL rrL m1).`1]
         (if Ver pkL (m1, ((Com pkL rL m1).`1, (Com pkL rL m1).`2)) 
          then ([(Com pkL rrL m1).`2], [m1])
          else ([FaultyO (Com pkL rrL m1).`1 pkL], [FaultyM (Com pkL rrL m1).`1 pkL])).`1) =
x \in zip ([(Com pkL rrL m1).`2], [m1]).`2 
      (zip [(Com pkL rrL m1).`1]  ([(Com pkL rrL m1).`2], [m1]).`1).
rewrite h => //=. progress.
have ->: x =  (m1, ((Com pkL rrL m1).`1, (Com pkL rrL m1).`2)). rewrite -H9 H8. 
have ->: ((Com pkL rrL m1).`1, (Com pkL rrL m1).`2) = Com pkL rrL m1. 
rewrite -pairS => //.
rewrite S_correct. apply H. 
have :  Ver pkL (m1, ((Com pkL rL m1).`1, (Com pkL rL m1).`2)). 
have ->: ((Com pkL rL m1).`1, (Com pkL rL m1).`2) = Com pkL rL m1. 
rewrite -pairS => //.
rewrite S_correct. apply H. move => b. rewrite b => //.
have :  Ver pkL (m1, ((Com pkL rL m1).`1, (Com pkL rL m1).`2)). 
have ->: ((Com pkL rL m1).`1, (Com pkL rL m1).`2) = Com pkL rL m1. 
rewrite -pairS => //.
rewrite S_correct. apply H. move => b. rewrite b => //.
have :  Ver pkL (m1, ((Com pkL rL m1).`1, (Com pkL rL m1).`2)). 
have ->: ((Com pkL rL m1).`1, (Com pkL rL m1).`2) = Com pkL rL m1. 
rewrite -pairS => //.
rewrite S_correct. apply H. move => b. rewrite b => //.
move => h. rewrite h.
have : Pr[ NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 ] =
Pr[ NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c = A.c' ] +  
Pr[ NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c <> A.c'].
rewrite Pr[mu_split NNMO_G0.c = A.c']. reflexivity.
move => h1.
have ->: Pr[NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c <> A.c'] =
Pr[NNMO_G0(A).main() @ &m : NNMO_G0.m = m1] -
Pr[NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c = A.c']. 
rewrite h1. 
have ->: Pr[NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c = A.c'] +
Pr[NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c <> A.c'] -
Pr[NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c = A.c'] = 
Pr[NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c <> A.c']. 
have f1 : forall (x y : real), x + y - x = y. progress. smt. 
progress. apply f1. auto.  
rewrite g0 =>//.  
qed.


local lemma g1 &m:
  Pr[ NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 ] = 1%r/4%r.
proof.
byphoare (_: _ ==> _) => //. 
proc. inline*.
seq 5 : (NNMO_G1.m = m1) (1%r/2%r) (1%r/2%r) (1%r/2%r) (0%r) (mdistr = duniform[m1; m2]).
rnd. wp. rnd. skip. progress. 
rnd. wp. rnd. skip. progress. 
rewrite duniformE. progress. 
case (m1 = m2). progress. 
have : m1 <> m2. apply m1_and_m2_diff. progress.  progress. 
rewrite eq_sym in H. rewrite H. 
rewrite b2i0 b2i1 =>//.
rewrite Dpk_ll => //.
seq 1 : (NNMO_G1.n = m1) (1%r/2%r) (1%r) (1%r/2%r) (0%r) (mdistr = duniform[m1; m2] /\ NNMO_G1.m = m1).
rnd. skip. progress.  
rnd. skip. progress. 
rewrite duniformE. progress. 
case (m1 = m2). progress. 
have : m1 <> m2. apply m1_and_m2_diff. progress.  progress. 
rewrite eq_sym in H. rewrite H. 
rewrite b2i0 b2i1 =>//.
wp. rnd. wp. rnd. skip. progress. 
rewrite Dr_ll =>//.
rewrite Dr_ll =>//.
wp. rnd. wp. rnd. skip. progress.  
rewrite mu0_false. progress. reflexivity.
rewrite Dr_ll =>//. progress.
hoare.
wp. rnd. wp. rnd. rnd.  skip. progress.
rewrite  negb_and. case(NNMO_G1.m{hr} <> m1). 
progress. simplify. move => h.
progress.
progress.
qed. 



local lemma g1a &m:
  Pr[ NNMO_G1(A).main() @ &m : res ] = 1%r/4%r
    -  Pr[ NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\  NNMO_G1.n = m1 /\ NNMO_G1.c = A.c'].
proof.
have : Pr[ NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c <> A.c'] =
  Pr[ NNMO_G1(A).main() @ &m : res ].
byequiv(_: _ ==> _) => //.
proc. inline*.  
wp. rnd. wp. rnd. rnd. rnd. wp. rnd. 
skip. progress.   
have : Ver pkL (m1, ((Com pkL rL m1).`1, (Com pkL rL m1).`2)).    
have ->: ((Com pkL rL m1).`1, (Com pkL rL m1).`2) = Com pkL rL m1. rewrite -pairS => //.
rewrite S_correct. apply H. move => b. 
have : x \in
     zip
       (if Ver pkL (m1, ((Com pkL rL m1).`1, (Com pkL rL m1).`2)) 
        then ([(Com pkL rrL m1).`2], [m1])
        else ([FaultyO (Com pkL rrL m1).`1 pkL], [FaultyM (Com pkL rrL m1).`1 pkL])).`2
       (zip [(Com pkL rrL m1).`1]
          (if Ver pkL (m1, ((Com pkL rL m1).`1, (Com pkL rL m1).`2)) 
           then ([(Com pkL rrL m1).`2], [m1])
           else ([FaultyO (Com pkL rrL m1).`1 pkL], [FaultyM (Com pkL rrL m1).`1 pkL])).`1) =
x \in zip ([(Com pkL rrL m1).`2], [m1]).`2 
      (zip [(Com pkL rrL m1).`1]  ([(Com pkL rrL m1).`2], [m1]).`1).
rewrite b => //=.  move => c.  
have : x \in zip ([(Com pkL rrL m1).`2], [m1]).`2 
             (zip [(Com pkL rrL m1).`1]  ([(Com pkL rrL m1).`2], [m1]).`1) = 
(x = (m1, ((Com pkL rrL m1).`1, (Com pkL rrL m1).`2))). progress. move => d. 
have :  (x = (m1, ((Com pkL rrL m1).`1, (Com pkL rrL m1).`2))). rewrite -d -c H10. 
move => r.  
rewrite r. auto.
have : Ver pkL (m1, ((Com pkL rrL m1).`1, (Com pkL rrL m1).`2)).    
have ->: ((Com pkL rrL m1).`1, (Com pkL rrL m1).`2) = Com pkL rrL m1. 
rewrite -pairS => //.
rewrite S_correct. apply H. progress.
have : Ver pkL (m1, ((Com pkL rL m1).`1, (Com pkL rL m1).`2)).   
have ->: ((Com pkL rL m1).`1, (Com pkL rL m1).`2) = Com pkL rL m1. 
rewrite -pairS => //.
rewrite S_correct. apply H. move => b. rewrite b => //.
have : Ver pkL (m1, ((Com pkL rL m1).`1, (Com pkL rL m1).`2)).   
have ->: ((Com pkL rL m1).`1, (Com pkL rL m1).`2) = Com pkL rL m1. 
rewrite -pairS => //.
rewrite S_correct. apply H. move => b. rewrite b => //.
have : Ver pkL (m1, ((Com pkL rL m1).`1, (Com pkL rL m1).`2)).   
have ->: ((Com pkL rL m1).`1, (Com pkL rL m1).`2) = Com pkL rL m1. 
rewrite -pairS => //.
rewrite S_correct. apply H. move => b. rewrite b => //.
clear H13 H12 H11 H10 H4 H2 H3 H8 H6 H2 H0.
case (mL = m1).  auto.
move => H14.
have :  mL = m2.
rewrite supp_duniform mem_seq2 in H1. 
elim H1 => [mL1 | mL2] => //.   
clear H14.  
move => mLem2.
have f1 :
  ((FaultyM (Com pkL rrL m1).`1 pkL), ((Com pkL rrL m1).`1, FaultyO (Com pkL rrL m1).`1 pkL)) \in
      zip
        (if Ver pkL (m1, ((Com pkL rL mL).`1, (Com pkL rL mL).`2)) 
         then ([(Com pkL rrL m1).`2], [m1])
         else ([FaultyO (Com pkL rrL m1).`1 pkL], [FaultyM (Com pkL rrL m1).`1 pkL])).`2
        (zip [(Com pkL rrL m1).`1]
           (if Ver pkL (m1, ((Com pkL rL mL).`1, (Com pkL rL mL).`2)) 
            then ([(Com pkL rrL m1).`2], [m1])
            else ([FaultyO (Com pkL rrL m1).`1 pkL], [FaultyM (Com pkL rrL m1).`1 pkL])).`1).
case (Ver pkL (m1, ((Com pkL rL mL).`1, (Com pkL rL mL).`2)) = false). 
move => q.  rewrite  q.
simplify. auto.
move => H10.  
have ->: Ver pkL (m1, ((Com pkL rL mL).`1, (Com pkL rL mL).`2)) = true. 
rewrite eqT. apply negbFE in H10. auto.
progress. 
have :  Ver pkL (m1, ((Com pkL rL mL).`1, (Com pkL rL mL).`2)) = false.
have ->: ((Com pkL rL mL).`1, (Com pkL rL mL).`2) = Com pkL rL mL. 
rewrite -pairS => //.
rewrite mLem2. 
rewrite S_inj. apply H. apply m1_and_m2_diff. progress.   
move => H11. progress.
have :  Ver pkL (m1, ((Com pkL rL mL).`1, (Com pkL rL mL).`2)) = false.
have ->: ((Com pkL rL mL).`1, (Com pkL rL mL).`2) = Com pkL rL mL. 
rewrite -pairS => //.
rewrite mLem2. 
rewrite S_inj. apply H. apply m1_and_m2_diff. progress.   
move => H11. progress.
have :  Ver pkL (m1, ((Com pkL rL mL).`1, (Com pkL rL mL).`2)) = false.
have ->: ((Com pkL rL mL).`1, (Com pkL rL mL).`2) = Com pkL rL mL. 
rewrite -pairS => //.
rewrite mLem2.
rewrite S_inj. apply H. apply m1_and_m2_diff. progress. progress. smt.        
move => a. rewrite -a. 
have : Pr[ NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 ] =
Pr[ NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c = A.c' ] +  
Pr[ NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c <> A.c'].
rewrite Pr[mu_split NNMO_G1.c = A.c'].
have ->: Pr[NNMO_G1(A).main() @ &m : (NNMO_G1.m = m1 /\ NNMO_G1.n = m1) /\ NNMO_G1.c = A.c']
 = Pr[NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c = A.c'].
rewrite Pr[mu_eq]. progress. auto. 
have ->: Pr[NNMO_G1(A).main() @ &m : (NNMO_G1.m = m1 /\ NNMO_G1.n = m1) /\ NNMO_G1.c <> A.c']
 = Pr[NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c <> A.c'].
rewrite Pr[mu_eq]. progress. auto.
progress. move => b.
have ->: Pr[NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c = A.c'] =
  Pr[NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1] -
  Pr[NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c <> A.c'].
rewrite b. smt. 
rewrite g1. 
have ->: 1%r / 4%r - 
(1%r / 4%r - Pr[NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c <> A.c']) =
Pr[NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c <> A.c']. smt. 
auto.  
qed.


local lemma df &m:
  1%r/4%r - 
  Pr[NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c = A.c'] +
  Pr[NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c = A.c'] =
  Pr[ NNMO_G0(A).main() @ &m : res ] - Pr[ NNMO_G1(A).main() @ &m : res ].
proof.
have : Pr[ NNMO_G0(A).main() @ &m : res ] - Pr[ NNMO_G1(A).main() @ &m : res ] = 
       1%r / 4%r - Pr[NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c = A.c'] + 
       Pr[NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c = A.c']. 
rewrite g0a g1a. smt. 
move => h6. rewrite h6. auto.  
qed.


local module N1 = {
   var n : message
   var m : message
   var c : commitment
 
   proc main() : bool = {
    var pk, x, mdistr, r, rr, rel0, rel, cs, ms, ds, d, y, d0;

    pk <$ Dpk;                                                                                                  
    x <- pk;                                                                                                    
    A.pk <- x;                                                                                                  
    mdistr <- duniform [m1; m2];                                                                                
    NNMO_G1.m <$ mdistr;                                                                                        
    NNMO_G1.n <$ mdistr;                                                                                        
    r <$ Dr;                                                                                                    
    (NNMO_G1.c, d) <- Com pk r NNMO_G1.m;                                                                       
    y <- NNMO_G1.c;                                                                                             
    A.c <- y;                                                                                                   
    rr <$ Dr;                                                                                                   
    (A.c', A.d') <- Com A.pk rr m1;                                                                             
    rel0 <- fun (x0 : message) (xs : message list) => x0 = m1 /\ head witness xs = m1;                          
    (rel, cs) <- (rel0, [A.c']);                                                                                
    d0 <- d;                                                                                                    
    (ds, ms) <- if Ver A.pk (m1, (A.c, d0)) 
                then ([A.d'], [m1]) 
                else ([FaultyO A.c' A.pk], [FaultyM A.c' A.pk]);
    return  (forall x, x \in zip ms (zip cs ds) => Ver pk x)
           /\ rel n ms
           /\ c \notin cs
           /\ size cs = size ds
           /\ size ms = size ds
           /\ cs <> [];
  }
}.

local module N2 = { 
   proc main() : bool = {
    var pk, x, mdistr, r, rr, rel0, rel, cs, ms, ds, d, y, d0;

    pk <$ Dpk;                                                                                                  
    x <- pk;                                                                                                    
    A.pk <- x;                                                                                                  
    mdistr <- duniform [m1; m2];                                                                                
    NNMO_G1.m <$ mdistr;                                                                                        
    NNMO_G1.n <$ mdistr;                                                                                        
    r <$ Dr;                                                                                                    
    (NNMO_G1.c, d) <- Com pk r NNMO_G1.m;                                                                       
    y <- NNMO_G1.c;                                                                                             
    A.c <- y;                                                                                                   
    rr <$ Dr;                                                                                                   
    (A.c', A.d') <- Com A.pk rr m1;                                                                             
    rel0 <- fun (x0 : message) (xs : message list) => x0 = m1 /\ head witness xs = m1;                          
    (rel, cs) <- (rel0, [A.c']);                                                                                
    d0 <- d;                                                                                                    
    (ds, ms) <- if Ver A.pk (m1, (A.c, d0)) 
                then ([A.d'], [m1]) 
                else ([FaultyO A.c' A.pk], [FaultyM A.c' A.pk]);
    return   NNMO_G1.m = m1
            /\ NNMO_G1.n = m1
            /\ NNMO_G1.c = A.c';
  }
}.

local lemma n &m:
  Pr[ NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c = A.c' ] =
  Pr[ N2.main() @ &m : res].
proof.
byequiv =>//. proc. inline*. 
wp. rnd. wp. rnd. rnd. rnd. wp. rnd. 
skip. progress.
qed.


local module N1T = {
   proc main(mm : message,a:unit) : bool = {
    var pk, x, mdistr, r, rr, rel0, rel, cs, ms, ds, d, y, d0;

    NNMO_G1.n <- mm;
    pk <$ Dpk;                                                                                                  
    x <- pk;                                                                                                    
    A.pk <- x;                                                                                                  
    mdistr <- duniform [m1; m2];                                                                                
    NNMO_G1.m <$ mdistr;                                                                                        
                                                                                        
    r <$ Dr;                                                                                                    
    (NNMO_G1.c, d) <- Com pk r NNMO_G1.m;                                                                       
    y <- NNMO_G1.c;                                                                                             
    A.c <- y;                                                                                                   
    rr <$ Dr;                                                                                                   
    (A.c', A.d') <- Com A.pk rr m1;                                                                             
    rel0 <- fun (x0 : message) (xs : message list) => x0 = m1 /\ head witness xs = m1;                          
    (rel, cs) <- (rel0, [A.c']);                                                                                
    d0 <- d;                                                                                                    
    (ds, ms) <- if Ver A.pk (m1, (A.c, d0)) 
                then ([A.d'], [m1]) 
                else ([FaultyO A.c' A.pk], [FaultyM A.c' A.pk]);
    return   NNMO_G1.m = m1
            /\ NNMO_G1.n = m1
            /\ NNMO_G1.c = A.c';
  }
}.


local module NN = {
  proc main() = {
    var n, r;
    n <$ duniform [m1; m2];
    r <- N1T.main(n,tt);
    return r;
  }
}.


local lemma gg &m:
  Pr[ NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c = A.c' ] =
  Pr[ N1.main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c = A.c' ].
proof.
byequiv => //. proc. inline*. 
wp. rnd. wp. rnd. rnd. rnd. wp. rnd. 
skip. progress.
qed. 


local lemma gg1 &m :
  Pr[ N2.main() @ &m : res ] = 
  Pr[ NN.main() @ &m : res ].  
proof.
byequiv =>//. proc. inline*.
wp. rnd. wp. rnd. rnd. 
swap{2} 4 4.
swap{2} 3 4.
swap{2} 2 4.
wp. swap {2} 1 1. rnd. wp. rnd. 
skip. progress. 
case(mL = m1). progress. 
case(nL = m1). progress.
progress. progress.
qed.  


local lemma gg3 &m :
    Pr[ N2.main() @ &m : res ] =
    1%r/2%r * Pr[ N1T.main(m1,tt) @ &m : res ] + 
    1%r/2%r * Pr[ N1T.main(m2,tt) @ &m : res ].
proof.
have : Pr[ N2.main() @ &m : res ]
       = Pr[ W(N1T).main() @ &m : res ].
byequiv => //. proc. inline*.  
wp. 
swap{2} 4 4.
swap{2} 3 4.
swap{2} 2 4.
rnd. wp. rnd. rnd. wp.  swap {2} 1 1. rnd. wp. rnd. 
skip. progress.
case(mL = m1). progress. 
case(nL = m1). progress.
progress. progress.
move => h. rewrite h.
apply (splitcases N1T).       
qed.
 

local lemma gg4 &m :
    Pr[ NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c = A.c' ] =
    1%r/2%r * Pr[ N1T.main(m1,tt) @ &m : res ] + 
    1%r/2%r * Pr[ N1T.main(m2,tt) @ &m : res ].
proof.
rewrite n gg3. reflexivity.
qed. 


local lemma g &m:
  Pr[NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c = A.c'] =
  1%r/2%r * Pr[N1T.main(m1,tt) @ &m : res].
proof.
rewrite gg4.
have ->: Pr[N1T.main(m2,tt) @ &m : res] = 0%r.
byphoare(_: arg = (m2, tt) ==> _) => //. hoare. 
proc. 
inline*. 
wp. rnd. wp. rnd. rnd. wp. rnd. wp.
skip. progress.
rewrite !negb_and.   
have : m1 <> m2. apply m1_and_m2_diff. rewrite eq_sym.
move => H3. rewrite H3. progress. 
apply invr0. 
qed.


module Q = {

  var c, c' : commitment

  proc main(m : message, a : unit) : bool = {
    var pk, r1, r2, d, d';    
    pk                 <$ Dpk;  
    r1                 <$ Dr;
    (c, d)             <- Com pk r1 m;
    r2                 <$ Dr;    
    (c', d')           <- Com pk r2 m;
    
    return c = c'; 
  }
}.


local module G = {
  
  var m : message

  proc main() : bool = {
    var v;                                                                                                                     
    m <$ duniform [m1; m2];                                                                                   
    v <- Q.main(m,tt);
    return v;

  }
}.


local lemma splitG &m:
  Pr[ G.main() @ &m : res ]
  = 1%r/2%r * Pr[ Q.main(m1,tt) @ &m : res ]
  + 1%r/2%r * Pr[ Q.main(m2,tt) @ &m : res ].
proof.
have :  Pr[ G.main() @ &m : res ] = Pr[ W(Q).main() @ &m : res ].
byequiv => //. proc. inline*. sim.
move => H. rewrite H.
apply (splitcases Q).       
qed. 

local lemma h &m:
  Pr[NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c = A.c'] =
  1%r/2%r * Pr[ Q.main(m1,tt) @ &m : res]. 
proof.
have ->: Pr[NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c = A.c'] = Pr[ G.main() @ &m : res /\ G.m = m1 ].
byequiv =>//. proc. inline*.
wp. rnd. wp. rnd.
swap {2} 4 -2.
wp. swap {2} 1 1. rnd. wp. rnd.
skip. progress.
byphoare(_: (glob Q) = (glob Q){m} ==> _) =>//. 
pose z := Pr[Q.main(m1,tt) @ &m : res].
proc.  
seq 1 : (G.m = m1) (1%r/2%r) z (1%r/2%r) 0%r.
rnd. skip. progress. 
rnd. skip. progress. 
rewrite duniformE. progress. 
case (m1 = m2). progress. 
have : m1 <> m2. apply m1_and_m2_diff. progress.  progress. 
rewrite eq_sym in H. rewrite H.
rewrite b2i0 b2i1 =>//.
have phr : phoare[ Q.main : arg = (m1,tt)  ==> res ] = Pr[Q.main(m1,tt) @ &m : res].
bypr. progress. byequiv. proc.
inline*. wp. rnd. wp. rnd. rnd. 
skip. progress.
have : m{m0} = m1. rewrite H. rewrite fst_pair. auto.
move => H6. rewrite H6. auto. auto. 
progress.
call phr.
skip. progress.
hoare. call(_:true). wp. rnd. wp. rnd. rnd.
skip. progress.
skip. progress.
have ->: G.m{hr} <> m1. apply H.
auto.
progress.
qed.


(* the adv of adversary is 1/4 - 1/4 * negligible value *)
lemma cnm_unsat &m:
  1%r/4%r - 
  1%r/4%r * Pr[ Q.main(m1,tt) @ &m : res ] =
  `|Pr[ NNMO_G0(A).main() @ &m : res ] - Pr[ NNMO_G1(A).main() @ &m : res ]|.
proof.
rewrite -df g. progress.
have ->:  Pr[N1T.main(m1,tt) @ &m : res] =
          Pr[NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c = A.c'].  
byequiv(_: _ ==> _) => //. proc. inline*. 
wp. rnd. wp. rnd. 
rnd. wp. rnd. wp. 
skip. progress.  
rewrite h.
have ->: (inv 4%r - 1%r / 2%r * Pr[Q.main(m1,tt) @ &m : res] + 1%r / 2%r * Pr[Q.main(m1,tt) @ &m : res] / 2%r) = 
(inv 4%r - 1%r / 4%r * Pr[Q.main(m1,tt) @ &m : res]). smt.
progress. smt.  
qed.


end section.
end CounterExample2.
