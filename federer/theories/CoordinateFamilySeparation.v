(** Federer (1969), 3.2.9, p. 247: the
    coordinate projection of 1.7.4, p. 31,
    can be chosen injective on the span
    of a finite independent family. This is
    the exterior-coordinate argument used on ker Df. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates ExteriorIndices FiniteExteriorPowers
  CoordinateProjection CoordinateProjectionVolume AssociatedInitialCoordinates GrassmannCoordinates
  CovectorProducts CovectorSimpleProducts SimpleWordIndependence AlternatingCoordinates AlternatingPairing
  IndependentProducts FiniteIndependence FiniteSpans LinearBasis TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [coordinate_projection_independent_family]:
    the appeal to 1.7.4 in Federer 3.2.9,
    p. 247. A nonzero top product has
    a nonzero Grassmann coordinate, making the
    corresponding projected family independent. Empty families
    and zero-dimensional spans are included. *)
Lemma coordinate_projection_independent_family (R:realType) m k
    (e:'I_k->R_n R m):
  finite_independent e -> exists lambda:Lambda m k,
    finite_independent (fun i=>coordinate_projection lambda (e i)).
Proof.
move=>he.
have h2:(1+1:R)!=0 by change (2%:R!=(0:R)); rewrite pnatr_eq0.
pose omega:=@euclidean_coordinate_covector R m.
have hDual i j:omega i [tuple @coordinate_basis R m j]=if i==j then 1 else 0.
  by rewrite /omega euclidean_coordinate_covectorE /coordinate_basis ffunE eq_sym.
pose xi:=e_lambda e (ord_tuple k).
have hXi:xi!=0:=@independent_product_nonzero R h2 (R_n R m) k e he.
have [lambda hLambda]:=@nonzero_Grassmann_coordinate R h2 (R_n R m) m k
  (@coordinate_basis R m) omega (@coordinate_basisP R m) hDual xi hXi.
exists lambda.
apply:nonzero_word_independent; apply:product_word_nonzero.
apply/eqP=>hZero; move:hLambda.
rewrite /xi_lambda /xi /omega coordinate_projection_volume_pairing hZero
  (bil0l (@pairing_bilinear R (R_n R k) R^o k)) eqxx.
by [].
Qed.

(** Source for [coordinate_projection_separates_finite_span]:
    the coordinate separation of the derivative kernel
    in Federer 3.2.9, p. 247. Vanishing
    projected coordinates force all coefficients and hence
    the original vector to vanish. *)
Lemma coordinate_projection_separates_finite_span (R:realType) m k
    (e:'I_k->R_n R m):
  finite_independent e -> exists lambda:Lambda m k,forall x,
    in_finite_span e x -> coordinate_projection lambda x=0 -> x=0.
Proof.
move=>he; have [lambda hLambda]:=coordinate_projection_independent_family he.
exists lambda=>x [c ->] hZero.
have hProjected:(\sum_i c i*:coordinate_projection lambda (e i))=0.
  have hEval:coordinate_projection lambda (\sum_i c i*:e i)=
      \sum_i c i*:coordinate_projection lambda (e i).
    rewrite linear_sum; apply:eq_bigr=>i _; exact:linearZ.
  by rewrite hEval in hZero.
have hCoeff:=hLambda c hProjected.
apply:big1=>i _; by rewrite hCoeff scale0r.
Qed.
