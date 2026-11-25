(** Federer (1969), 4.1.17, p. 374: finite-mass flat
    currents are exactly the mass closure of supported normal
    currents. Contraction by every variation-summable differential
    form preserves the original compact flat index. The public
    statements use the original current, variation and contraction;
    the supporting proofs reuse the preceding flat and L1 laws. *)
From Federer Require Export FlatFiniteMassClosure
  FlatCurrentMassLimits FlatCurrentSmoothContraction
  CurrentVariationFormLone FlatCurrentMeasurableContraction.
