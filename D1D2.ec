pragma Goals:printall.
require import Distr DBool List Real Int.

theory D1D2.

type message.

module D1 = {
  proc sample(m1 : message, m2 : message) = {
    var m;
    m <$ duniform [m1; m2]      ;
    return m;
  }
}.

module D2 = {
  proc sample(m1 : message, m2 : message) = {
    var b;
    b <$ {0,1};
    return if b then m2 else m1;
  }
}.

section.


local lemma qm3 &m m1 m2 : Pr[ D1.sample(m1, m2) @ &m : res = m2 \/ res = m1 ] = 1%r.
proof. byphoare (_: arg = (m1 , m2) ==> _) => //. proc.  rnd. 
skip.  progress.
case(m1{hr} <> m2{hr}). move => a. 
rewrite duniformE => /=. rewrite a => /=. rewrite b2i1 => //=.   
rewrite duniformE => //.  
qed.


local lemma qm4 &m m1 m2 : Pr[ D2.sample(m1, m2) @ &m : res = m2 \/ res = m1 ] = 1%r.
proof. byphoare (_: arg = (m1, m2) ==> _) => //. proc.  rnd. 
skip.  progress. 
case (m1{hr} <> m2{hr}). move => a. 
rewrite duniformE => /=. rewrite b2i1 => //=.
rewrite duniformE => //=. rewrite b2i1 => //. 
qed.



local lemma qm1 &m &n m1 m2 : m1 <> m2 => Pr[ D1.sample(m1, m2) @ &m : res = m1 ] = Pr[D2.sample(m1, m2) @ &n : res = m1 ].
proof. move => m1_and_m2_diff.  byequiv => //. proc*. inline*. wp.
rnd (fun (x : message) => if x = m1 then false else true) (fun (x : bool) => if x then m2 else m1).
wp. skip.  progress.   
case bR.
move => _. 
rewrite eq_sym in m1_and_m2_diff. rewrite m1_and_m2_diff => //. progress.

have : mu1 {0,1} true = 1%r/2%r.
rewrite duniformE => //=. rewrite b2i1 b2i0 => //=. progress. 

case bR => // b.
rewrite H1 duniformE => /=. rewrite m1_and_m2_diff => /=. 
rewrite b2i1. have : !(pred1 m2 m1). progress. move => ->. rewrite b2i0 => //. 
rewrite duniformE => /=. rewrite b2i1 b2i0 => /=.  
rewrite duniformE => /=. rewrite m1_and_m2_diff => /=. 
rewrite b2i1. have : !(pred1 m1 m2). rewrite eq_sym in m1_and_m2_diff => //. move => ->. rewrite b2i0 => //. 
 
case (mL = m1). move => -> =>//. progress => //. 
rewrite supp_duniform mem_seq2 in H1. 
elim H1 => [mL1 | mL2] => //.   
rewrite H2 => //. 
qed.



local lemma qm2 &m &n m1 m2 : m1 <> m2 => Pr[ D1.sample(m1,m2) @ &m : res = m2 ] = Pr[D2.sample(m1,m2) @ &n : res = m2 ].
proof. move => m1_and_m2_diff.  byequiv => //. proc*. inline*. wp.
rnd (fun (x : message) => if x = m1 then false else true) (fun (x : bool) => if x then m2 else m1).
wp. skip.  progress.    
case bR.
move => _.
rewrite eq_sym in m1_and_m2_diff. by rewrite m1_and_m2_diff.  progress. 

have : mu1 {0,1} true = 1%r/2%r.
rewrite duniformE => //=. by rewrite b2i1 b2i0. progress.

case bR => // b.
rewrite H1 duniformE => /=. rewrite m1_and_m2_diff => /=. 
rewrite b2i1. have : !(pred1 m2 m1). progress. move => ->. rewrite b2i0 => //. 
rewrite duniformE => /=. rewrite b2i1 b2i0 => /=.  
rewrite duniformE => /=. rewrite m1_and_m2_diff => /=. 
rewrite b2i1. have : !(pred1 m1 m2). rewrite eq_sym in m1_and_m2_diff => //. move => ->. by rewrite b2i0. 

case (mL = m1). move => -> =>//. progress => //. 
rewrite supp_duniform mem_seq2 in H1. 
elim H1 => [mL1 | mL2] => //. 
by rewrite -H2.
by rewrite H2. 
qed.


local lemma q1q2neq w1 w2 : w1 <> w2 =>
   equiv [D1.sample ~ D2.sample : ={arg} /\ m1{1} = w1 /\ m2{1} = w2 /\ m1{2} = w1 /\ m2{2} = w2 /\ w1{1} = w1 /\ w2{2} = w2 ==> ={res} ].
proof. progress.
  bypr res{1} res{2} => //.
progress.
rewrite H2 H1. 
case (a = m1{1}) => e. rewrite e.
apply qm1.
apply H.  
case (a = m2{1}) => f. rewrite f. 
apply qm2. apply H.
have f1 : Pr[D1.sample(m1{1}, m2{1}) @ &1 : (res = a) \/ (res = m2{1} \/ res = m1{1})] = 1%r. 
   have : Pr[D1.sample(m1{1},m2{1}) @ &1 : (res = m2{1} \/ res = m1{1})] <=
   Pr[D1.sample(m1{1},m2{1}) @ &1 : (res = a) \/ (res = m2{1} \/ res = m1{1})].
   rewrite Pr[mu_sub]. smt. auto. progress. 
have : Pr[ D1.sample(m1{1}, m2{1}) @ &1 : res = m2{1} \/ res = m1{1} ] = 1%r. apply qm3. progress. smt.

have f2 : Pr[D1.sample(m1{1},m2{1}) @ &1 : (res = a) \/ (res = m2{1} \/ res = m1{1})]
  = Pr[D1.sample(m1{1},m2{1}) @ &1 : res = a ]
  + Pr[D1.sample(m1{1}, m2{1}) @ &1 :  (res = m2{1} \/ res = m1{1})].
  rewrite Pr[mu_disjoint]. smt. auto.
have ->: Pr[D1.sample(m1{1}, m2{1}) @ &1 : res = a] = Pr[D1.sample(m1{1}, m2{1}) @ &1 : res = a \/ res = m2{1} \/ res = m1{1}] - Pr[D1.sample(m1{1}, m2{1}) @ &1 : res = m2{1} \/ res = m1{1}]. smt. rewrite f1 qm3. progress.

have g1 : Pr[D2.sample(m1{1}, m2{1}) @ &2 : (res = a) \/ (res = m2{1} \/ res = m1{1})] = 1%r. 
   have : Pr[D2.sample(m1{1},m2{1}) @ &2 : (res = m2{1} \/ res = m1{1})] <=
   Pr[D2.sample(m1{1},m2{1}) @ &2 : (res = a) \/ (res = m2{1} \/ res = m1{1})].
   rewrite Pr[mu_sub]. smt. auto. progress. 
have : Pr[ D2.sample(m1{1}, m2{1}) @ &2 : res = m2{1} \/ res = m1{1} ] = 1%r. apply qm4. progress. smt.

have g2 : Pr[D2.sample(m1{1},m2{1}) @ &2 : (res = a) \/ (res = m2{1} \/ res = m1{1})]
  = Pr[D2.sample(m1{1},m2{1}) @ &2 : res = a ]
  + Pr[D2.sample(m1{1}, m2{1}) @ &2 :  (res = m2{1} \/ res = m1{1})].
  rewrite Pr[mu_disjoint]. smt. auto.
have ->: Pr[D2.sample(m1{1}, m2{1}) @ &2 : res = a] = Pr[D2.sample(m1{1}, m2{1}) @ &2 : res = a \/ res = m2{1} \/ res = m1{1}] - Pr[D2.sample(m1{1}, m2{1}) @ &2 : res = m2{1} \/ res = m1{1}]. smt. rewrite g1 qm4. progress.
qed.


local lemma q1q2eq : 
   equiv [D1.sample ~ D2.sample : ={arg} /\ arg.`1{1} = arg.`2{1} ==> ={res} ].
proof. proc. rnd {1}. rnd{2}.
skip. progress. apply duniform_ll => //. rewrite supp_duniform in H1. rewrite mem_seq2 in H1.
elim H1 => [m01 | m02] => //. 
qed.


local lemma q1q2e w1 w2 :
  equiv [D1.sample ~ D2.sample : ={arg} /\ m1{1} = w1 /\ m2{1} = w2  ==> ={res} ].
proof. case (w1 = w2) => e.
conseq q1q2eq => //.  
conseq (q1q2neq w1 w2 e) => //.
qed.



lemma q1q2 :
  equiv [D1.sample ~ D2.sample : ={arg}  ==> ={res} ].
proof. 
conseq (_: (exists w1 w2, arg{1} = (w1,w2)) /\ ={arg} ==> _).
progress. smt. 
elim*.
progress. conseq (q1q2e w1 w2) => //. 
qed.


end section.
end D1D2.
