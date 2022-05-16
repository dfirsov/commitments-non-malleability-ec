require import AllCore List Distr Commitment.

require  NSNM_Definition.


type value, commitment, openingkey, message, advice.
type snm_relation = message -> message -> bool.

op Com (pk : value) (m : message) : (commitment * openingkey) distr.
op Ver : value -> message * (commitment * openingkey) -> bool.
op Dpk : value distr.


clone export NSNM_Definition as NSNM_def  with type value  <- value,
                                           type message    <- message,
                                           type commitment <- commitment,
                                           type openingkey <- openingkey,
                                           op Com <- Com,
                                           op Ver <- Ver,
                                           op Dpk <- Dpk.



clone import CommitmentProtocol as CP with type value      <- value,
                                           type message    <- message,
                                           type commitment <- commitment,
                                           type openingkey <- openingkey.





(* Creszenzo style simulation-based non-malleability  *)
module C_SEG0(CS:CommitmentScheme, A : AdvSNM) = {
  proc main(rel : snm_relation, md : message distr) : bool = {
    var pk, c,c',d,d',m,m',v;    
    pk                 <- CS.gen(); 
    m                  <$ md;
    (c, d)             <- CS.commit(pk, m);
    c'                 <- A.commit(c, rel);
    (d', m')           <- A.decommit(d);    
    v                  <- CS.verify(pk, m', c', d');
    return v /\ rel m m' /\ c <> c';
  }
}.
module C_SEG1(CS:CommitmentScheme, S : Simulator) = {
  proc main(rel : snm_relation, md : message distr) : bool = {
    var m,m',pk;    
    pk                 <- CS.gen(); 
    m                  <$ md;
    m'           <- S.simulate(pk, rel, md);
    return rel m m';
  }
}.



section.

declare module C : CommitmentScheme.
declare module A : AdvSNM {C}.
declare module S : Simulator {C}.

op ler : snm_relation.
op md : message distr.

module H(A : AdvSNM) = {
  proc init(pk : value, h : advice) : (message distr) * snm_relation = {
        return (md, ler);
    }
  proc commit(c : commitment, r : snm_relation) : commitment = {
      var q;
      q <- A.commit(c,r);
      return q;
  }
  proc decommit(d : openingkey) : openingkey * message = {
      var w;
      w <- A.decommit(d);
      return w;
  }
}.


local lemma qq1 &m : Pr[ C_SEG0(C,A).main(ler,md) @ &m : res ] <= Pr[ SEG0(C,H(A)).main(witness) @ &m : res ].
proof.
byequiv =>//. proc. inline*. 
call (_:true).
wp.  call (_:true).
wp. call (_:true).
wp.  call (_:true).
rnd. wp. call (_:true). skip. progress.
smt.
qed.


local lemma qq2 &m : Pr[ C_SEG1(C,S).main(ler,md) @ &m : res ] = Pr[ SEG1(C,H(A),S).main(witness) @ &m : res ].
proof.
byequiv =>//. proc. inline*. 
call (_:true).
rnd. wp.   call (_:true).
skip. progress.
qed.


lemma cresc_to_nsnm  &m :
  Pr[ C_SEG0(C,A).main(ler,md) @ &m : res ] - Pr[ C_SEG1(C,S).main(ler,md) @ &m : res ]
 <= Pr[ SEG0(C,H(A)).main(witness) @ &m : res ] - Pr[ SEG1(C,H(A),S).main(witness) @ &m : res ].
proof.
smt.
qed.
end section.


(* Arita style simulation-based non-malleability  *)
module A_SEG0(A : AdvSNM) = {
  proc main(rel : snm_relation, md : message distr) : bool = {
    var pk,c,c',d,d',m,m',v;    
    pk                 <$ Dpk; 
    m                  <$ md;
    (c, d)             <$ Com pk m;
    c'                 <- A.commit(c, rel);
    (d', m')           <- A.decommit(d);    
    v                  <- Ver pk (m', (c',d'));
    return v /\ rel m m' /\ m <> m';
  }
}.


module A_SEG1(S : Simulator) = {
  proc main(rel : snm_relation, md : message distr) : bool = {
    var m,m',pk;    
    pk                 <$ Dpk; 
    m                  <$ md;
    m'                 <- S.simulate(pk, rel, md);
    return rel m m' /\ m <> m';
  }
}.



section.

declare module A : AdvSNM.
declare module S : Simulator.

op aler : snm_relation.
op amd : message distr.

axiom ler_antirefl m m' :  aler m m' => m <> m'.

module AT(A : AdvSNM) = {
  proc init(pk : value, h : advice) : (message distr) * snm_relation = {
        return (amd, aler);
    }
  proc commit(c : commitment, r : snm_relation) : commitment = {
      var q;
      q <- A.commit(c,r);
      return q;
  }
  proc decommit(d : openingkey) : openingkey * message = {
      var w;
      w <- A.decommit(d);
      return w;
  }
}.

axiom S_inj pk m1 m2 c d: pk \in Dpk => m1 <> m2 => (c,d) \in Com pk m2 => !Ver pk (m1, (c, d)).

local lemma qq1 &m : Pr[ A_SEG0(A).main(aler,amd) @ &m : res ] <= Pr[ SG0(AT(A)).main(witness) @ &m : res ].
proof.
byequiv =>//. proc. inline*.
wp. call (_:true).
wp.  call (_:true).
wp. rnd. rnd. 
wp. rnd. skip. progress.
smt.
qed.


local lemma qq2 &m : Pr[ A_SEG1(S).main(aler,amd) @ &m : res ] = Pr[ SG1(AT(A),S).main(witness) @ &m : res ].
proof.
byequiv=>//. proc. inline*. 
call (_:true). rnd. wp. rnd.
skip. progress.
smt. 
qed.

lemma arita_to_nsnm  &m :
  Pr[ A_SEG0(A).main(aler,amd) @ &m : res ] - Pr[ A_SEG1(S).main(aler,amd) @ &m : res ]
 <= Pr[ SG0(AT(A)).main(witness) @ &m : res ] - Pr[ SG1(AT(A),S).main(witness) @ &m : res ].
proof.
smt.
qed.

end section.




