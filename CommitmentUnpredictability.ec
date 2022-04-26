
require import AllCore List. 

type value, commitment, openingkey, message.

op Com (pk : value) (m : message) : (commitment * openingkey) distr.
op Ver : value -> message * (commitment * openingkey) -> bool.
op Dpk : value distr.

module type Guesser = {
  proc guess(pk : value) : message * (commitment * openingkey) list
}.


(* Guesser-adversary tries to compute a list "l" which would contain a
canonically generated commitment-opening pair. *)
module UnpredGame(G : Guesser) = {
  proc main() = {
    var pk,m,l,c,d;
    pk      <$ Dpk;
    (m, l) <- G.guess(pk); 
    (c, d)  <$ Com pk m;
    return (c,d) \in l;
  }
}.
