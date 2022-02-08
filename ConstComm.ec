pragma Goals:printall.
require import DBool List Real.
require import Commitment.
require import Distr AllCore.



require  LRO.

theory CrescenzoSNM.

type message.
require NSNM_Related.

clone import NSNM_Related as NSNM_rel  with type value  <- unit,
                                           type message    <- message,
                                           type commitment <- unit,
                                           type openingkey <- message.



clone import CommitmentProtocol as CP with type value      <- unit,
                                           type message    <- message,
                                           type commitment <- unit,
                                           type openingkey <- message.



module ConstComm = {
  proc gen() : unit = {
    return tt;
  }

  proc commit(pk : unit, m : message) : unit * message = {
    return (tt, m);
  }

  proc verify(pk : unit, m : message, c : unit, d : message) = {
    return m = d;
  }
}.


section.

declare module A : AdvSNM.

lemma lll &m : 
 Pr[ C_SEG0(ConstComm,A).main(ler,md) @ &m : res ] = 0%r.
byphoare =>//. hoare. proc.
inline*. wp.  
conseq (_: _ ==> true).
call (_:true). call (_:true). wp. rnd. wp.
skip. auto.
qed.


(* ConstComm satisfies the non-malleability by Crescenzo et al. *)
lemma cresc_const_comm &m : forall (S <: Simulator),  Pr[ C_SEG0(ConstComm,A).main(ler,md) @ &m : res ]
 - Pr[ C_SEG1(ConstComm,S).main(ler,md) @ &m : res ] <= 0%r.
proof. move => S. rewrite lll. smt. 
qed.

end section.
end CrescenzoSNM.
 

theory AirtaSNM.

type message = bool.


op Dpk : unit distr.
op Ver (pk : unit) (mum :  message * (unit * message)) :  bool 
 = mum.`1 = mum.`2.`2.
op Com (x : unit) (r : bool list) (m : message) : unit * message
 = (tt,m).

axiom Dpk_ll : is_lossless Dpk.

clone import NSNM_Related as NSNM_rel  with type value  <- unit,
                                           type message    <- message,
                                           type commitment <- unit,
                                           type openingkey <- message,
                                           op Dpk <- Dpk,
                                           op Ver <- Ver,
                                           op Com <- Com.


clone import CommitmentProtocol as CP with type value      <- unit,
                                           type message    <- message,
                                           type commitment <- unit,
                                           type openingkey <- message.


module AritaA : AdvSNM = {

  proc init(pk : unit, h : advice) : (message distr) * snm_relation = {
    return witness;
  }
  proc commit(pk : unit, r : snm_relation) : unit = {
    return tt;
  } 

  proc decommit(d : message) : message * message = {
     return (!d, !d); 
  }
  
}.



op myrel = fun (m1 m2 : message) => m1 <> m2.
op myd = duniform [false;true].

lemma qq &m : Pr[ A_SEG0(AritaA).main(myrel,myd) @ &m : res ] = 1%r.
proof. byphoare (_: arg = (myrel, myd) ==> _) =>//. proc.
inline*. rewrite /Ver. wp.  simplify.
seq 3 : (rel = myrel /\ md = myd).
rnd. rnd. rnd. skip. auto. rnd.  rnd.  rnd.  skip.  progress. smt. smt. smt. skip .  progress.
smt.
smt. hoare. simplify.
rnd. rnd. rnd. skip. auto. auto. 
qed.

section.

declare module S : Simulator.

axiom S_ll : islossless S.simulate.


lemma pp &m : Pr[ A_SEG1(S).main(myrel,myd) @ &m : res ] = 1%r/2%r.
proof. byphoare (_: arg = (myrel, myd) ==> _) =>//. proc.
swap 2 1.
seq 2 :  true 1%r (1%r/2%r)   (1%r/2%r) 0%r (rel = myrel /\ md = myd) .
call (_:true). rnd. skip.  auto.
call (_:true). apply S_ll. rnd. skip. smt.
rnd. skip. progress.
rewrite /myrel.
have ->: (fun (x : message) => x <> m'{hr} /\ x <> m'{hr})
 = (fun (x : message) => x <> m'{hr}).
apply fun_ext. smt.
rewrite /myd.
rewrite duniformE. smt.
exfalso. auto. auto. 
qed.


(* ConstComm is malleable according to the definition of non-mall. by Arita *)
lemma arita_const_comm &m : Pr[ A_SEG0(AritaA).main(myrel,myd) @ &m : res ]
 - Pr[ A_SEG1(S).main(myrel,myd) @ &m : res ] = 1%r/2%r.
proof. smt. qed.

end section.
end AirtaSNM.
