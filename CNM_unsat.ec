pragma Goals:printall. 

require import AllCore DBool List Distr Real Int. 
require import Commitment.
require WholeMsg D1D2.

theory NM.

type value,  message,  commitment, openingkey.
type relation = message -> message list -> bool.

clone import CommitmentProtocol as CP with type value      <- value,
                                           type message    <- message,
                                           type commitment <- commitment,
                                           type openingkey <- openingkey.

op Dpk : value distr.
op Com (pk : value) (m : message) : (commitment * openingkey) distr.
op Ver : value -> message * (commitment * openingkey) -> bool.
op mdistr : message distr.

abbrev (\notin) ['a] (z : 'a) (s : 'a list) : bool = !mem s z.

axiom S_correct pk m c d: pk \in Dpk => (c,d) \in Com pk m => Ver pk (m, (c, d)).
axiom S_inj pk m1 m2 c d: pk \in Dpk => m1 <> m2 => (c,d) \in Com pk m2 => !Ver pk (m1, (c, d)).

axiom Com_ll pk m : is_lossless (Com pk m).
axiom Dpk_ll : is_lossless Dpk.
axiom mdistr_ll : is_lossless mdistr.

module type AdvNNMO = {
  proc init(pk : value) : message distr
  proc commit(c : commitment) : relation * commitment list
  proc decommit(d : openingkey) : openingkey list * message list
}.


module NNMO_G0(A : AdvNNMO) = {
  var m : message
  var c : commitment

  proc main() : bool = {
    var rel, pk, mdistr, d, cs, ds, ms;    
    pk                 <$ Dpk;  
    mdistr             <- A.init(pk);
    m                  <$ mdistr;
    (c, d)             <$ Com pk m;
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
    var rel, pk, mdistr, d, cs, ds, ms;    
    pk                 <$ Dpk;                    
    mdistr             <- A.init(pk);
    m                  <$ mdistr;
    n                  <$ mdistr;       
    (c, d)             <$ Com pk m;
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
    var rel;
    
    c <- y;
    (c', d') <$ Com pk m1;    
    rel <- fun (x : message) (xs : message list)
                     => x = m1 /\ head witness xs = m1;
    return (rel, [c']);
  }

  proc decommit(d : openingkey) : openingkey list * message list = {
    var c2, d2;

    (c2, d2) <$ Com pk m2;
    return (if Ver pk (m1, (c, d)) then ([d'], [m1])
                                   else ([d2], [m2]));  
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
wp. rnd. wp. rnd. wp. rnd. skip. progress. 
rewrite Com_ll => //. rewrite Com_ll => //. rewrite Com_ll => //.
hoare.
wp. rnd. wp. rnd. wp. rnd. skip. progress. progress.
qed.    


local lemma g0a &m : Pr[ NNMO_G0(A).main() @ &m : res ] = 1%r/2%r -  
  Pr[ NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c = A.c'].
proof.
have :  Pr[ NNMO_G0(A).main() @ &m : res ] = 
Pr[ NNMO_G0(A).main() @ &m : NNMO_G0.m = m1 /\ NNMO_G0.c <> A.c']. 
byequiv(_: _ ==> _) => //. proc. inline*.
wp.  rnd.  wp.  rnd.  wp. rnd.  rnd. wp. rnd. simplify.
skip. progress.    
have : Ver pkL (m1, (cdL.`1, cdL.`2)). 
have : (c'd'L.`1, c'd'L.`2) \in Com pkL m1. rewrite -pairS =>//.
rewrite S_correct. apply H. rewrite -pairS. apply H3. progress.
move => h.
have :  Ver pkL (m1, (cdL.`1, cdL.`2)). rewrite S_correct. 
apply H. rewrite -pairS. apply H3. progress. 
have : x \in zip
       (if Ver pkL (m1, (cdL.`1, cdL.`2)) then ([c'd'L.`2], [m1])
        else ([c2d2L.`2], [m2])).`2
       (zip [c'd'L.`1]
          (if Ver pkL (m1, (cdL.`1, cdL.`2)) then ([c'd'L.`2], [m1])
           else ([c2d2L.`2], [m2])).`1) =
x \in zip ([c'd'L.`2], [m1]).`2 (zip  [c'd'L.`1] ([c'd'L.`2], [m1]).`1 ).
rewrite h => //=. progress.   
have ->: x = (m1, (c'd'L.`1, c'd'L.`2)). rewrite -H12. apply H10.       
rewrite S_correct. apply H. rewrite -pairS => //.
have :  Ver pkL (m1, (cdL.`1, cdL.`2)). rewrite S_correct. 
apply H. rewrite -pairS. apply H3. progress. 
rewrite H10 =>//.
have :  Ver pkL (m1, (cdL.`1, cdL.`2)). rewrite S_correct. 
apply H. rewrite -pairS. apply H3. progress. 
rewrite H10 =>//.
have :  Ver pkL (m1, (cdL.`1, cdL.`2)). rewrite S_correct. 
apply H. rewrite -pairS. apply H3. progress. 
rewrite H10 =>//.         
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
wp. rnd. wp. rnd. wp. rnd. skip. progress. 
rewrite Com_ll =>//. rewrite Com_ll =>//. rewrite Com_ll =>//. 
hoare.
wp. rnd. wp. rnd. wp. rnd. skip. progress.   
progress. hoare.  
wp. rnd. wp. rnd. wp. rnd. rnd. skip. progress. rewrite H.
progress. progress. 
qed. 



local lemma g1a &m:
  Pr[ NNMO_G1(A).main() @ &m : res ] = 1%r/4%r
    -  Pr[ NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\  NNMO_G1.n = m1 /\ NNMO_G1.c = A.c'].
proof.
have : Pr[ NNMO_G1(A).main() @ &m : NNMO_G1.m = m1 /\ NNMO_G1.n = m1 /\ NNMO_G1.c <> A.c'] =
  Pr[ NNMO_G1(A).main() @ &m : res ].
byequiv(_: _ ==> _) => //.
proc. inline*.  
wp. rnd. wp. rnd. wp. rnd. rnd. rnd. wp. rnd. 
skip. progress.    
have : Ver pkL (m1, (cdL.`1, cdL.`2)). 
have : (cdL.`1, cdL.`2) \in Com pkL m1. rewrite -pairS =>//.
rewrite S_correct. apply H. rewrite -pairS. apply H5. progress. move => h1.  
have : x \in zip
       (if Ver pkL (m1, (cdL.`1, cdL.`2)) then ([c'd'L.`2], [m1])
        else ([c2d2L.`2], [m2])).`2
       (zip [c'd'L.`1]
          (if Ver pkL (m1, (cdL.`1, cdL.`2)) then ([c'd'L.`2], [m1])
           else ([c2d2L.`2], [m2])).`1) =
       x \in zip ([c'd'L.`2], [m1]).`2 (zip [c'd'L.`1] ([c'd'L.`2], [m1]).`1 ).
rewrite h1 =>//=. progress. 
have : x = (m1, (c'd'L.`1, c'd'L.`2)). rewrite -H13. apply H12. progress.
rewrite S_correct. apply H. rewrite -pairS. apply H7.
have :  Ver pkL (m1, (cdL.`1, cdL.`2)). rewrite S_correct. 
apply H. rewrite -pairS. apply H5. progress. rewrite H12 =>//.        
have :  Ver pkL (m1, (cdL.`1, cdL.`2)). rewrite S_correct. 
apply H. rewrite -pairS. apply H5. progress. rewrite H12 =>//.
have :  Ver pkL (m1, (cdL.`1, cdL.`2)). rewrite S_correct. 
apply H. rewrite -pairS. apply H5. progress. rewrite H12 =>//.      
case (mL = m1).  auto.
move => H16.
have :  mL = m2.
rewrite supp_duniform mem_seq2 in H1. 
elim H1 => [mL1 | mL2] => //.     
move => mLem2.   
have : Ver pkL (mL, (cdL.`1, cdL.`2)). apply S_correct. apply H0. rewrite -pairS. rewrite H5.
progress. rewrite mLem2. rewrite S_correct. apply H. rewrite -pairS. rewrite -mLem2 H5. smt. 
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
progress. rewrite H. auto.
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
    var pk, x, mdistr, rel0, rel, cs, ms, ds, d, y, d0, c2, d2;

    pk <$ Dpk;                                                                                                  
    x <- pk;                                                                                                    
    A.pk <- x;                                                                                                  
    mdistr <- duniform [m1; m2];                                                                                
    NNMO_G1.m <$ mdistr;                                                                                        
    NNMO_G1.n <$ mdistr;                                                                                                                                                                          
    (NNMO_G1.c, d) <$ Com pk NNMO_G1.m;                                                                       
    y <- NNMO_G1.c;                                                                                             
    A.c <- y;                                                                                                                                                                                                    
    (A.c', A.d') <$ Com A.pk m1;                                                                             
    rel0 <- fun (x0 : message) (xs : message list) => x0 = m1 /\ head witness xs = m1;                          
    (rel, cs) <- (rel0, [A.c']);                                                                                
    d0 <- d;                   
    (c2, d2) <$ Com A.pk m2;             
    (ds, ms) <- if Ver A.pk (m1, (A.c, d0)) then ([A.d'], [m1])        
                                            else ([d2], [m2]);  
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
    var pk, x, mdistr, rel0, rel, cs, ms, ds, d, y, d0, c2, d2;

    pk <$ Dpk;                                                                                                  
    x <- pk;                                                                                                    
    A.pk <- x;                                                                                                  
    mdistr <- duniform [m1; m2];                                                                                
    NNMO_G1.m <$ mdistr;                                                                                        
    NNMO_G1.n <$ mdistr;                                                                                        
                                                                                                
    (NNMO_G1.c, d) <$ Com pk NNMO_G1.m;                                                                       
    y <- NNMO_G1.c;                                                                                             
    A.c <- y;                                                                                                   
                                                                                                  
    (A.c', A.d') <$ Com A.pk m1;                                                                             
    rel0 <- fun (x0 : message) (xs : message list) => x0 = m1 /\ head witness xs = m1;                          
    (rel, cs) <- (rel0, [A.c']);                                                                                
    d0 <- d;                   
    (c2, d2) <$ Com A.pk m2;             
    (ds, ms) <- if Ver A.pk (m1, (A.c, d0)) then ([A.d'], [m1])        
                                            else ([d2], [m2]);  
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
wp. rnd. wp. rnd. wp. rnd. rnd. rnd. wp. rnd. 
skip. progress.
qed.


local module N1T = {
   proc main(mm : message,a:unit) : bool = {
    var pk, x, mdistr, rel0, rel, cs, ms, ds, d, y, d0, c2, d2;

    NNMO_G1.n <- mm;
    pk <$ Dpk;                                                                                                  
    x <- pk;                                                                                                    
    A.pk <- x;                                                                                                  
    mdistr <- duniform [m1; m2];                                                                                
    NNMO_G1.m <$ mdistr;                                                                                        
                                                                                        
                                                                                                       
    (NNMO_G1.c, d) <$ Com pk NNMO_G1.m;                                                                       
    y <- NNMO_G1.c;                                                                                             
    A.c <- y;                                                                                                   
                                                                                                      
    (A.c', A.d') <$ Com A.pk m1;                                                                             
    rel0 <- fun (x0 : message) (xs : message list) => x0 = m1 /\ head witness xs = m1;                          
    (rel, cs) <- (rel0, [A.c']);                                                                                
    d0 <- d;                   
    (c2, d2) <$ Com A.pk m2;             
    (ds, ms) <- if Ver A.pk (m1, (A.c, d0)) then ([A.d'], [m1])        
                                            else ([d2], [m2]); 
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
wp. rnd. wp. rnd. wp. rnd. rnd. rnd. wp. rnd. 
skip. progress.
qed. 


local lemma gg1 &m :
  Pr[ N2.main() @ &m : res ] = 
  Pr[ NN.main() @ &m : res ].  
proof.
byequiv =>//. proc. inline*.
wp. rnd. wp. rnd.  
swap{2} 4 4.
swap{2} 9 -1.
swap{2} 2 6.
wp. swap {2} 1 6. rnd. wp. rnd. rnd. wp. rnd. wp. 
skip. progress. 
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
swap{2} 2 4. swap{2} 1 4. 
rnd. wp. rnd. swap{1} 6 -1. wp. rnd. rnd. wp. rnd. wp. rnd. 
skip. progress.
move => H. rewrite H.
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
wp. rnd. wp. rnd. wp. rnd. rnd. wp. rnd. wp. 
skip. progress.
rewrite !negb_and.   
have : m1 <> m2. apply m1_and_m2_diff. rewrite eq_sym.
move => H4. rewrite H4. progress. 
apply invr0. 
qed.


module Q = {

  var c, c' : commitment

  proc main(m : message, a : unit) : bool = {
    var pk, d, d';    
    pk                 <$ Dpk;  
    (c, d)             <$ Com pk m;
    (c', d')           <$ Com pk m;
    
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
swap {2} 4 -3. swap {2} 4 -2. wp. 
seq 5 3 : (pk{1} \in Dpk /\ ={pk} /\ A.pk{1} = pk{1} /\ mdistr{1} = duniform [m1; m2] /\ NNMO_G0.m{1} \in duniform [m1; m2] /\ G.m{2} \in duniform [m1; m2] /\ NNMO_G0.m{1} = G.m{2}).
rnd. wp. rnd. skip. progress. sp.
case(m{2} = m2). 
conseq (_: _ ==>  NNMO_G0.m{1} <> m1 /\ G.m{2} <> m1). progress.
rnd. wp. rnd {1}. wp. rnd.  skip. progress. rewrite Com_ll. rewrite eq_sym. apply m1_and_m2_diff.  
rewrite eq_sym. apply m1_and_m2_diff.  
rnd{1}. wp. rnd. wp. rnd. skip. progress. 
smt. smt. rewrite Com_ll.   
byphoare(_: (glob Q) = (glob Q){m} ==> _) =>//. 
pose z := Pr[Q.main(m1,tt) @ &m : res].
proc.  
seq 1 : (G.m = m1) (1%r/2%r) z (1%r/2%r) 0%r.
rnd. skip. progress. 
rnd. skip. progress. 
rewrite duniformE. progress. 
case (m1 = m2). progress. 
have : m1 <> m2. apply m1_and_m2_diff. progress. progress. 
rewrite eq_sym in H. rewrite H.
rewrite b2i0 b2i1 =>//.
have phr : phoare[ Q.main : arg = (m1,tt)  ==> res ] = Pr[Q.main(m1,tt) @ &m : res].
bypr. progress. byequiv. proc.
rnd. rnd. rnd. 
skip. progress.
have : m{m0} = m1. rewrite H. rewrite fst_pair. auto.
move => H6. rewrite H6. auto. smt. smt. smt. progress.
call phr.
skip. progress.
hoare. call(_:true). wp. rnd. wp. rnd. rnd.
skip. progress.
skip. progress.
have ->: G.m{hr} <> m1. apply H. auto.
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
wp. rnd. rnd. wp. rnd. wp. 
skip. progress.  
rewrite h.
have ->: (inv 4%r - 1%r / 2%r * Pr[Q.main(m1,tt) @ &m : res] + 1%r / 2%r * Pr[Q.main(m1,tt) @ &m : res] / 2%r) = 
(inv 4%r - 1%r / 4%r * Pr[Q.main(m1,tt) @ &m : res]). smt.
progress. smt.  
qed.


end section.
end CounterExample2.



