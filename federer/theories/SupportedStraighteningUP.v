(** Federer (1969), 3.1.23, pp. 236–237: an
    ambient diffeomorphism straightens B to its affine tangent
    plane inside a controlled ball and fixes the exterior. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormDiffeomorphismUP TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_controlled_tangent_straightening]: the complete
    conclusion of Federer 3.1.23, pp. 236–237. The
    affine plane A= b+Tan(B,b) is expressed by subtracting b.
    f and g are actual mutually inverse global class-k maps;
    both Lipschitz constants and the exact local membership
    equivalence are obligations, not assumed existence axioms. *)
Record is_controlled_tangent_straightening (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) (B:X->Prop) b t r (f g:X->X) k : Prop := {
  (** Source for [controlled_straightening_diffeomorphism]: global
      class-k diffeomorphism, Federer 3.1.23, p. 236. *)
  controlled_straightening_diffeomorphism:is_norm_diffeomorphism hN hN
    (fun _=>True) (fun _=>True) f g k;
  (** Source for [controlled_straightening_forward_lipschitz]: Lip(f)
      is at most 1/t, Federer 3.1.23, p. 236. *)
  controlled_straightening_forward_lipschitz:forall x y,N (f x-f y)<=t^-1*N (x-y);
  (** Source for [controlled_straightening_inverse_lipschitz]: Lip(g)
      is at most 1/t, Federer 3.1.23, p. 236. *)
  controlled_straightening_inverse_lipschitz:forall x y,N (g x-g y)<=t^-1*N (x-y);
  (** Source for [controlled_straightening_fixed_exterior]: f is
      identity outside the open radius-r ball, Federer 3.1.23,
      pp. 236–237, including its boundary. *)
  controlled_straightening_fixed_exterior:forall x,r<=N (x-b) -> f x= x;
  (** Source for [controlled_straightening_local_plane]: the exact
      equality U(b,tr) intersect B= U(b,tr) intersect f inverse(A),
      Federer 3.1.23, p. 236. *)
  controlled_straightening_local_plane:forall x,N (x-b)<t*r ->
    (B x <-> norm_tangent_cone N B b (f x-b))
}.
