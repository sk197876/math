(** Federer (1969), 3.2.9, p. 247: kernel
    frame existence for the appeal to 1.7.4,
    p. 31. Use the opaque epimorphism coordinate
    chart from 3.1.3(3), p. 213. All
    frame witnesses remain local existential proofs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates FiniteIndependence FiniteBasisComparison
  FiniteSpans LinearBasis EuclideanBlockLinearMaps EuclideanBlockCoordinates EuclideanBlockLinear
  EuclideanEpimorphismBlockChart EuclideanKernelFrameUP EuclideanCoordinateTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_epimorphism_kernel_frame_exists]:
    dimension and basis of ker Df in the
    proof of Federer 3.2.9, p. 247.
    The inverse linear chart sends the last-coordinate
    basis to a kernel frame satisfying its independent
    specification. No kernel frame is assumed. *)
Theorem euclidean_epimorphism_kernel_frame_exists (R:realType) n k
    (L:Hom (R_n R (n+k)) (R_n R n)):
  (forall y,exists x,L x=y) -> exists e,is_euclidean_kernel_frame L e.
Proof.
move=>hSurj.
have [beta [gamma [hBG [hGB hHead]]]]:=@euclidean_epimorphism_block_chart_exists R n k
  (hom_as_linear L) hSurj.
pose K:=hom_comp gamma (@euclidean_last_injection_map R n k).
have hKin:injective K.
  move=>x y hEq.
  have hGamma:injective gamma:=can_inj hGB.
  have hInc:@euclidean_last_injection R n k x=@euclidean_last_injection R n k y.
    apply:hGamma; exact hEq.
  have hh:=congr1 (@euclidean_last_block R n k) hInc.
  by rewrite !euclidean_last_block_injectionK in hh.
pose e:=fun i:'I_k=>K (@coordinate_basis R k i).
exists e; split.
- exact (@finite_independent_map R [the finType of 'I_k] (R_n R k) (R_n R (n+k))
    (hom_as_linear K) (@coordinate_basis R k) hKin (finite_basis_independent (@coordinate_basisP R k))).
- move=>x; split.
  + move=>hL.
    have hFirst:@euclidean_first_block R n k (beta x)=0.
      rewrite hHead; exact hL.
    have hRec:@euclidean_last_injection R n k (@euclidean_last_block R n k (beta x))=beta x.
      have hh:=@euclidean_block_linear_decomposition R n k (beta x).
      have hZeroInc:@euclidean_first_injection R n k 0=0.
        change (@euclidean_first_injection_map R n k 0=0); exact:linear0.
      rewrite hFirst hZeroInc add0r in hh; exact:Logic.eq_sym hh.
    have hK:K (@euclidean_last_block R n k (beta x))=x.
      change (gamma (@euclidean_last_injection R n k (@euclidean_last_block R n k (beta x)))=x).
      by rewrite hRec hBG.
    exists (fun i=>(@euclidean_last_block R n k (beta x)) i).
    rewrite -{1}hK -{1}(euclidean_coordinate_expansion (@euclidean_last_block R n k (beta x))).
    rewrite linear_sum; apply:eq_bigr=>i _; by rewrite linearZ.
  + move=>[c ->]; rewrite linear_sum.
    apply:big1=>i _; rewrite linearZ /e /K hom_compE.
    have hZero:L (gamma (@euclidean_last_injection R n k (@coordinate_basis R k i)))=0.
      by rewrite -hHead hGB euclidean_first_block_last_injection.
    change (c i*:L (gamma (@euclidean_last_injection R n k (@coordinate_basis R k i)))=0).
    by rewrite hZero scaler0.
Qed.
