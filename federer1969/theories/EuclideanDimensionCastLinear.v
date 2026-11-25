(** Federer (1969), 4.1.8, pp. 361–362: the original
    coordinate identifications across equal arithmetic dimensions
    use the already defined dimension cast of 2.6.5,
    p. 120. Its linear and norm laws change no values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormRegularity NormRegularityOperations InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanCoordinateLists.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_dimension_cast_linear]: linearity
    of the existing equal-dimension coordinate identification,
    supporting the product associativity of Federer 4.1.8,
    p. 361. *)
Lemma euclidean_dimension_cast_linear (R:realType) m n (e:m=n):
  linear (@euclidean_dimension_cast R m n e).
Proof. by case:n /e=>c x y. Qed.

(** Source for [euclidean_dimension_cast_map]: the original
    equal-dimension identification as a linear map, supporting
    Federer 4.1.8, pp. 361–362. This is an
    alias of the existing cast, with no selected coordinates. *)
Definition euclidean_dimension_cast_map (R:realType) m n (e:m=n):Hom (R_n R m) (R_n R n):=
  @HomMap R (R_n R m) (R_n R n) (@euclidean_dimension_cast R m n e)
    (introT (asboolP _) (@euclidean_dimension_cast_linear R m n e)).

(** Source for [euclidean_dimension_cast_norm]: the existing
    identification preserves the original Euclidean norm,
    supporting Federer 4.1.8, p. 361. *)
Lemma euclidean_dimension_cast_norm (R:realType) m n (e:m=n) (x:R_n R m):
  inner_norm (@euclidean_inner_productP R n) (@euclidean_dimension_cast_map R m n e x)=
    inner_norm (@euclidean_inner_productP R m) x.
Proof. by case:n /e. Qed.

(** Source for [euclidean_dimension_cast_bounded]: the original
    identification has homogeneous norm bound one, supporting
    Federer 4.1.8, p. 361, including dimension zero. *)
Lemma euclidean_dimension_cast_bounded (R:realType) m n (e:m=n):
  norm_bounded_linear (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) (@euclidean_dimension_cast_map R m n e).
Proof. exists 1;split;first exact:ler01;move=>x;by rewrite euclidean_dimension_cast_norm mul1r. Qed.

(** Source for [euclidean_dimension_cast_smooth]: the original
    equal-dimension identification is smooth on every original
    open source, supporting Federer 4.1.8, p. 361. *)
Theorem euclidean_dimension_cast_smooth (R:realType) m n (e:m=n)
    (U:set (R_n R m))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) U x):
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) U (@euclidean_dimension_cast_map R m n e).
Proof.
move=>k;exact:(@norm_class_linear R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R n))
  U (@euclidean_dimension_cast_map R m n e) k hU (@euclidean_dimension_cast_bounded R m n e)).
Qed.

(** Source for [euclidean_dimension_cast_differential]: the
    actual differential is the original identification itself,
    supporting Federer 4.1.8, pp. 361–362. *)
Theorem euclidean_dimension_cast_differential (R:realType) m n (e:m=n)
    (U:set (R_n R m))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) U x) x:
  U x->has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) U (@euclidean_dimension_cast_map R m n e) x
      (@euclidean_dimension_cast_map R m n e).
Proof.
move=>hx;apply:(@norm_differential_linear R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R n))
  U x (@euclidean_dimension_cast_map R m n e) (@hU x hx)).
exact:(@euclidean_dimension_cast_bounded R m n e).
Qed.
