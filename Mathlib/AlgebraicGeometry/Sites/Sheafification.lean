import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct

universe r t w v u

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {X : C}

lemma Limits.IsTerminal.subsingleton_forget [HasForget C]
    [PreservesLimit (Functor.empty.{0} C) (forget C)]
    {X : C} (h : IsTerminal X) :
    Subsingleton ((forget C).obj X) :=
  (Types.isTerminalEquivIsoPUnit _ <| h.isTerminalObj (forget C) X).toEquiv.subsingleton

def Limits.Cofan.isColimitMapCoconeEquiv {D : Type*} [Category D] (F : C ⥤ D)
    {ι : Type*} (X : ι → C) (c : Cofan X) :
    IsColimit (F.mapCocone c) ≃ IsColimit (Cofan.mk _ fun i ↦ F.map (c.inj i)) :=
  (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm (F.mapCocone c)).symm.trans <|
    IsColimit.equivIsoColimit (Cocones.ext (Iso.refl _))

def Limits.Fan.isLimitMapConeEquiv {D : Type*} [Category D] (F : C ⥤ D)
    {ι : Type*} (X : ι → C) (c : Fan X) :
    IsLimit (F.mapCone c) ≃ IsLimit (Fan.mk _ fun i ↦ F.map (c.proj i)) :=
  (IsLimit.postcomposeHomEquiv Discrete.natIsoFunctor (F.mapCone c)).symm.trans <|
    IsLimit.equivIsoLimit (Cones.ext (Iso.refl _))

section

variable (J : GrothendieckTopology C) [J.Subcanonical]
variable {ι : Type r} (X : ι → C)
variable {c : Cofan X} (hc : IsColimit c) (H : (Sieve.ofArrows _ c.inj) ∈ J c.pt)

lemma eq_of_eq
    (s : Cofan fun i ↦ J.yoneda.obj (X i))
    {Y : C} {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (hab : a ≫ c.inj i = b ≫ c.inj j)
    [∀ i, Mono (c.inj i)]
    (Hdisj : ∀ {i j : ι} (_ : i ≠ j) {Y : C} (a : Y ⟶ X i)
      (b : Y ⟶ X j) (_ : a ≫ c.inj i = b ≫ c.inj j), Nonempty (IsInitial Y))
    (hempty : (Y : C) → IsInitial Y → ⊥ ∈ J Y) :
    (s.inj i).val.app (op Y) a = (s.inj j).val.app (op Y) b := by
  by_cases h : i = j
  · subst h
    obtain rfl := (cancel_mono _).mp hab
    rfl
  · obtain ⟨h⟩ := Hdisj h a b hab
    exact (Sheaf.isTerminalOfBotCover s.pt _ (hempty Y h)).subsingleton_forget.elim _ _

@[simps]
def Sieve.toFunctor {X : C} (S : Sieve X) {Y : C} (f : Y ⟶ X) (hf : S f) :
    yoneda.obj Y ⟶ S.functor where
  app Z g := ⟨g ≫ f, S.downward_closed hf g⟩

noncomputable
def isColimit_cofanMk_yoneda
    [∀ (i : ι), Mono (c.inj i)]
    (hempty : (Y : C) → IsInitial Y → ⊥ ∈ J Y)
    (Hdisj : ∀ {i j : ι} (_ : i ≠ j) {Y : C} (a : Y ⟶ X i)
    (b : Y ⟶ X j), a ≫ c.inj i = b ≫ c.inj j → Nonempty (IsInitial Y)) :
    IsColimit (Cofan.mk _ fun i ↦ J.yoneda.map (c.inj i)) := by
  refine mkCofanColimit _ (fun s ↦ ⟨?_⟩) (fun s j ↦ ?_) fun s m hm ↦ ?_
  · refine (s.pt.2.isSheafFor (Sieve.ofArrows _ c.inj) H).extend ?_
    refine ⟨fun Y g ↦ ((s.inj (Sieve.ofArrows.i g.2)).val.app Y) (Sieve.ofArrows.h g.2), ?_⟩
    · intro ⟨Y⟩ ⟨Z⟩ ⟨(g : Z ⟶ Y)⟩
      ext u
      simp only [Sieve.functor_obj, Sieve.generate_apply, GrothendieckTopology.yoneda_obj_val,
        types_comp_apply, Sieve.functor_map_coe]
      rw [← eq_of_eq (J := J) _ s (g ≫ Sieve.ofArrows.h u.2)
        (Sieve.ofArrows.h <| Sieve.downward_closed _ u.2 g) (by simp) Hdisj hempty]
      apply congrFun ((s.inj _).val.naturality g.op)
  · ext : 1
    let u (j : ι) : yoneda.obj (X j) ⟶ (Sieve.ofArrows _ c.inj).functor :=
      (Sieve.ofArrows _ c.inj).toFunctor (c.inj j) (Sieve.ofArrows_mk _ _ j)
    have (j : ι) : u j ≫ (Sieve.ofArrows _ c.inj).functorInclusion = yoneda.map (c.inj j) :=
      rfl
    simp only [GrothendieckTopology.yoneda_obj_val, Cofan.mk_pt, cofan_mk_inj, Sieve.functor_obj,
      Sieve.generate_apply, Sheaf.comp_val, GrothendieckTopology.yoneda_map_val, ← this,
      Category.assoc, Presieve.IsSheafFor.functorInclusion_comp_extend]
    ext Z (g : Z.unop ⟶ X j)
    have h : Sieve.ofArrows X c.inj (g ≫ c.inj j) :=
      Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ j) _
    exact eq_of_eq (J := J) _ s (Sieve.ofArrows.h h) g (by simp) Hdisj hempty
  · ext : 1
    dsimp only [Cofan.mk_pt, GrothendieckTopology.yoneda_obj_val, id_eq, Sieve.functor_obj,
      Sieve.generate_apply]
    apply Presieve.IsSheafFor.unique_extend
    ext Y ⟨g, hg⟩
    simp [← hm (Sieve.ofArrows.i hg)]

instance [MonoCoprod C] [∀ {κ : Type r}, HasColimitsOfShape (Discrete κ) C]
    {ι : Type r} (X : ι → C)
    (H : ∀ {c : Cofan X} (hc : IsColimit c), Sieve.ofArrows _ c.inj ∈ J c.pt) :
    PreservesColimit (Discrete.functor X) J.yoneda := by
  constructor
  intro (c : Cofan X) hc
  constructor
  refine (Limits.Cofan.isColimitMapCoconeEquiv _ _ _).symm ?_
  have : ∀ i, Mono (c.inj i) := sorry
  refine isColimit_cofanMk_yoneda _ _ (H hc) ?_ ?_
  · sorry
  · sorry

-- what is the correct spelling? depending small refactor of `MonoCoprod` and co.
lemma foo [MonoCoprod C] [∀ {κ : Type r}, HasColimitsOfShape (Discrete κ) C]
    {ι : Type r} :
    PreservesColimitsOfShape (Discrete ι) J.yoneda := by
  apply (config := { allowSynthFailures := true }) preservesColimitsOfShape_of_discrete
  refine fun X ↦ ⟨fun {c : Cofan X} hc ↦ ⟨?_⟩⟩
  refine (Limits.Cofan.isColimitMapCoconeEquiv _ _ _).symm ?_
  have : ∀ (i : ι), Mono (c.inj i) := sorry
  refine isColimit_cofanMk_yoneda _ _ ?_ ?_ ?_
  · sorry
  · sorry
  · sorry

#exit
end

structure _root_.CategoryTheory.Presieve.GenerateStruct (R : Presieve X) (S : Sieve X) where
  obj {Y : C} (f : Y ⟶ X) (hf : S f) : C
  l {Y : C} (f : Y ⟶ X) (hf : S f) : Y ⟶ obj f hf
  r {Y : C} (f : Y ⟶ X) (hf : S f) : obj f hf ⟶ X
  l_comp_r {Y : C} (f : Y ⟶ X) (hf : S f) : l f hf ≫ r f hf = f := by aesop_cat
  r_mem {Y : C} (f : Y ⟶ X) (hf : S f) : R (r f hf)

lemma _root_.CategoryTheory.Presieve.nonempty_generateStruct_of_le
    (R : Presieve X) (S : Sieve X) (h : S ≤ Sieve.generate R) :
    Nonempty (R.GenerateStruct S) := by
  constructor
  exact ⟨fun f hf ↦ (h _ hf).choose,
    fun f hf ↦ (h _ hf).choose_spec.choose,
    fun f hf ↦ (h _ hf).choose_spec.choose_spec.choose,
    fun f hf ↦ (h _ hf).choose_spec.choose_spec.choose_spec.2,
    fun f hf ↦ (h _ hf).choose_spec.choose_spec.choose_spec.1⟩

attribute [reassoc (attr := simp)] Presieve.GenerateStruct.l_comp_r

lemma Functor.initial_of_isCofiltered_of_isThin {D : Type*} [Category D] {F : C ⥤ D}
    [IsCofiltered C] (H : ∀ (d : D), ∃ (c : C), Nonempty (F.obj c ⟶ d)) [Quiver.IsThin D] :
    F.Initial := by
  refine ⟨fun d ↦ ?_⟩
  obtain ⟨c, ⟨f⟩⟩ := H d
  have : Nonempty (CostructuredArrow F d) := ⟨.mk f⟩
  refine isConnected_of_zigzag fun i j ↦ ?_
  let x := IsCofiltered.min i.left j.left
  let xi := IsCofiltered.minToLeft i.left j.left
  let xj := IsCofiltered.minToRight i.left j.left
  refine ⟨[.mk (F.map xi ≫ i.hom), j], ?_, by simp⟩
  simp only [List.chain_cons, List.Chain.nil, and_true]
  exact ⟨.of_inv <| CostructuredArrow.homMk xi,
    .of_hom <| CostructuredArrow.homMk xj <| Subsingleton.elim ..⟩

lemma Sieve.generate_mono {X : C} {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂) :
    Sieve.generate R₁ ≤ Sieve.generate R₂ :=
  Sieve.giGenerate.gc.monotone_l h

lemma Presieve.monotone_functorPullback {D : Type*} [Category D] (F : C ⥤ D) (X : C) :
    Monotone (Presieve.functorPullback F (X := X)) := by
  intro R₁ R₂ hle Y f hf
  exact hle _ hf

def GrothendieckTopology.Cover.functorPullback
    {D : Type*} [Category D] (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsCocontinuous J K] (X : C) :
    K.Cover (F.obj X) ⥤ J.Cover X :=
  letI f (R : K.Cover (F.obj X)) : J.Cover X := ⟨Sieve.functorPullback F R.1, F.cover_lift _ _ R.2⟩
  Monotone.functor (f := f) <| by
    intro R S
    apply Sieve.functorPullback_monotone

instance {D : Type*} [Category D] (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsCocontinuous J K]
    [F.EssSurj] [F.Full] (X : C) :
    (GrothendieckTopology.Cover.functorPullback F J K X).Full := by
  constructor
  intro R S f
  exact ⟨homOfLE ((Sieve.essSurjFullFunctorGaloisInsertion F X).u_le_u_iff.mp (leOfHom f)), rfl⟩

def GrothendieckTopology.pullbackIso
    {J : GrothendieckTopology C} {X Y : C} (f : Y ≅ X) :
    J.Cover X ≌ J.Cover Y where
  functor := J.pullback f.hom
  inverse := J.pullback f.inv
  unitIso := (J.pullbackId X).symm ≪≫ eqToIso (by simp) ≪≫ J.pullbackComp f.inv f.hom
  counitIso := (J.pullbackComp f.hom f.inv).symm ≪≫ eqToIso (by simp) ≪≫(J.pullbackId Y)

instance {J : GrothendieckTopology C} {X Y : C} (f : Y ⟶ X) [IsIso f] :
    (J.pullback f).IsEquivalence :=
  inferInstanceAs <| (J.pullbackIso (asIso f)).functor.IsEquivalence

namespace Pretopology

variable [HasPullbacks C]

-- this does not work
def toGrothendieck' (J : Pretopology C) : GrothendieckTopology C where
  sieves X S := ∃ R ∈ J X, Sieve.generate R = S
  top_mem' X := by
    use Presieve.singleton (𝟙 X)
    simp [J.has_isos (𝟙 X)]
  pullback_stable' X Y S f := by
    rintro ⟨R, hR, rfl⟩
    use R.pullbackArrows f
    refine ⟨?_, ?_⟩
    · exact J.pullbacks f R hR
    · exact Sieve.pullbackArrows_comm f R
  transitive' := by
    rintro X - ⟨R, hR, rfl⟩ S H
    choose T hT heq using H
    use R.bind (fun Y f hf ↦ T (Sieve.le_generate _ _ hf))
    refine ⟨?_, ?_⟩
    · apply J.transitive _ _ hR
      intro Y f hf
      apply hT
    · ext Y g
      refine ⟨?_, ?_⟩
      · rintro ⟨Z, u, v, ⟨W, o, r, hr, ho, rfl⟩, rfl⟩
        have := heq (Sieve.le_generate _ _ hr)
        rw [← Category.assoc]
        show Sieve.pullback r S (u ≫ o)
        rw [← this]
        apply Sieve.downward_closed
        exact Sieve.le_generate _ _ ho
      · intro hg
        simp [Presieve.bind]
        sorry

/-- A cover of `X` in the pretopology `J` is a `J`-presieve on `X`. This is
a type synonym for `J X`, but `J.Cover X` is endowed with a different preorder. -/
def Cover (J : Pretopology C) (X : C) : Type (max u v) := J X

variable (J : Pretopology C) (X : C)

@[simp]
lemma generate_mem_toGrothendieck {X : C} {R : Presieve X} (h : R ∈ J X) :
    Sieve.generate R ∈ J.toGrothendieck C X :=
  ⟨R, h, Sieve.le_generate R⟩

/-- The preorder on `J.Cover X`. This is defined such that `R ≤ S` holds
if and only if `Sieve.generate R ≤ Sieve.generate S` holds. -/
instance : _root_.LE (J.Cover X) where
  le R S := ∀ {Y : C} (f : Y ⟶ X) (_ : R.1 f),
    ∃ (Z : C) (g : Z ⟶ X) (_ : S.1 g) (h : Y ⟶ Z), h ≫ g = f

variable {J X} in
lemma Cover.le_iff_generate_le_generate {R S : J.Cover X} :
    R ≤ S ↔ Sieve.generate R.1 ≤ Sieve.generate S.1 := by
  refine ⟨fun hle ↦ ?_, fun hle ↦ ?_⟩
  · intro Z g ⟨Y, u, v, hv, h⟩
    obtain ⟨W, o, ho, s, rfl⟩ := hle _ hv
    exact ⟨_, u ≫ s, o, ho, by simpa⟩
  · intro Y f hr
    obtain ⟨Z, g, o, ho, hgo⟩ : Sieve.generate S.1 f := hle _ <| Sieve.le_generate _ _ hr
    use Z, o, ho, g

instance : Preorder (J.Cover X) where
  le_refl := by simp [Cover.le_iff_generate_le_generate]
  le_trans a b c := by simpa [Cover.le_iff_generate_le_generate] using le_trans

instance : Nonempty (J.Cover X) := ⟨⟨.singleton (𝟙 X), J.has_isos (𝟙 X)⟩⟩

instance : IsDirected (J.Cover X) fun x y ↦ x ≥ y where
  directed R S := by
    let Ti ⦃Y : C⦄ (f : Y ⟶ X) (hf : R.1 f) : Presieve Y :=
      Presieve.pullbackArrows f S.1
    let T := R.1.bind Ti
    refine ⟨⟨T, ?_⟩, ?_, ?_⟩
    · exact J.transitive _ _ R.2 fun Y f H ↦ J.pullbacks _ _ S.2
    · intro Y f ⟨Z, u, v, hv, _, hf⟩
      use Z, v, hv, u
    · intro Y f ⟨Z, u, v, hv, hvu, hf⟩
      obtain ⟨Z, g, hg⟩ := hvu
      use Z, g, hg, pullback.fst g v
      rwa [pullback.condition]

@[simps]
def Cover.toGrothendieck (R : J.Cover X) : J.toGrothendieck.Cover X :=
  ⟨Sieve.generate R.1, by simp⟩

lemma Cover.monotone_toGrothendieck : Monotone (Cover.toGrothendieck J X) :=
  fun {_ _} hle ↦ Cover.le_iff_generate_le_generate.mp hle

@[simps! obj]
def toCover : J.Cover X ⥤ J.toGrothendieck.Cover X :=
  (Cover.monotone_toGrothendieck J X).functor

instance (X : C) : (J.toCover X).Full := by
  refine ⟨fun {R S} f ↦ ?_⟩
  suffices h : R ≤ S by exact ⟨homOfLE h, Subsingleton.elim _ _⟩
  rw [Cover.le_iff_generate_le_generate]
  exact leOfHom f

instance (X : C) : (J.toCover X).Initial := by
  refine Functor.initial_of_isCofiltered_of_isThin fun R ↦ ?_
  obtain ⟨S, hS, hle⟩ := R.2
  exact ⟨⟨S, hS⟩, ⟨(homOfLE <| (Sieve.generate_le_iff _ _).mpr hle)⟩⟩

instance [EssentiallySmall.{w} C] : EssentiallySmall.{w} (J.Cover X) :=
  let e := equivSmallModel C
  let F : J.Cover X ⥤ (J.toGrothendieck C).Cover X := J.toCover X
  let E :
      (J.toGrothendieck C).Cover X ⥤ (toGrothendieck C J).Cover (e.inverse.obj (e.functor.obj X)) :=
    (J.toGrothendieck C).pullback (e.unitIso.app X).inv
  let G' := GrothendieckTopology.Cover.functorPullback e.inverse
    (e.inverse.inducedTopology <| J.toGrothendieck C) (J.toGrothendieck C) (e.functor.obj X)
  have : EssentiallySmall.{w}
      ((e.inverse.inducedTopology (toGrothendieck C J)).Cover (e.functor.obj X)) :=
    essentiallySmall_of_small_of_locallySmall _
  essentiallySmall_of_fully_faithful.{w} (F ⋙ E ⋙ G')

variable {J} {X}

structure Cover.Arrow (R : J.Cover X) where
  Y : C
  f : Y ⟶ X
  hf : R.1 f

def Cover.Arrow.toGrothendieck {R : J.Cover X} {S : (J.toGrothendieck C).Cover X}
    (hle : R.1 ≤ S) (a : R.Arrow) :
    S.Arrow where
  Y := a.Y
  f := a.f
  hf := hle _ a.hf

noncomputable
def Cover.Arrow.relationToGrothendieck {R : J.Cover X} {S : (J.toGrothendieck C).Cover X}
    (hle : R.1 ≤ S) (a b : R.Arrow) :
    S.Relation where
  fst := a.toGrothendieck hle
  snd := b.toGrothendieck hle
  r.Z := pullback a.f b.f
  r.g₁ := pullback.fst _ _
  r.g₂ := pullback.snd _ _
  r.w := pullback.condition

@[simps]
def Cover.shape {X : C} (R : J.Cover X) : MulticospanShape where
  L := R.Arrow
  R := R.Arrow × R.Arrow
  fst I := I.fst
  snd I := I.snd

open Opposite

@[simps]
noncomputable
def Cover.index {D : Type*} [Category D] (R : J.Cover X) (P : Cᵒᵖ ⥤ D) :
    MulticospanIndex R.shape D where
  left (A : R.Arrow) := P.obj (op A.Y)
  right A := P.obj (op (pullback A.1.f A.2.f))
  fst _ := P.map (pullback.fst _ _).op
  snd _ := P.map (pullback.snd _ _).op

variable (R : J.Cover X) (S : (J.toGrothendieck C).Cover X) (hle : R.1 ≤ S)
variable {D : Type*} [Category D] (P : Cᵒᵖ ⥤ D)
variable (s : Multifork (R.index P)) (hs : IsLimit s)

variable (gen : R.1.GenerateStruct S)

@[simps]
def _root_.CategoryTheory.Presieve.GenerateStruct.arrow {R : J.Cover X}
    {S : (J.toGrothendieck C).Cover X} (gen : R.1.GenerateStruct S)
    (A : S.Arrow) :
    R.Arrow where
  Y := gen.obj A.f A.hf
  f := gen.r A.f A.hf
  hf := gen.r_mem A.f A.hf

@[simps! pt]
noncomputable
def multifork : Multifork (S.index P) := by
  refine Multifork.ofι _ ?_ ?_ ?_
  · exact s.pt
  · intro (A : S.Arrow)
    exact s.ι (gen.arrow A) ≫ P.map (gen.l A.f A.hf).op
  · intro b
    dsimp only [GrothendieckTopology.Cover.index_right, GrothendieckTopology.Cover.shape_fst,
      GrothendieckTopology.Cover.index_left, GrothendieckTopology.Cover.shape_L, Cover.index_left,
      Presieve.GenerateStruct.arrow_Y, GrothendieckTopology.Cover.index_fst,
      GrothendieckTopology.Cover.shape_snd, GrothendieckTopology.Cover.index_snd]
    have := s.condition ⟨gen.arrow b.fst, gen.arrow b.snd⟩
    dsimp only [Cover.index_right, Presieve.GenerateStruct.arrow_Y, Presieve.GenerateStruct.arrow_f,
      Cover.shape_fst, Cover.index_left, Cover.index_fst, Cover.shape_snd, Cover.index_snd] at this
    let g : b.r.Z ⟶ pullback (gen.r b.fst.f b.fst.hf) (gen.r b.snd.f b.snd.hf) :=
      pullback.lift (b.r.g₁ ≫ gen.l b.fst.f b.fst.hf) (b.r.g₂ ≫ gen.l b.snd.f b.snd.hf)
        (by simp [b.r.w])
    have h1 : g ≫ pullback.fst _ _ = _ := pullback.lift_fst _ _ _
    have h2 : g ≫ pullback.snd _ _ = _ := pullback.lift_snd _ _ _
    rw [Category.assoc, ← Functor.map_comp, ← op_comp]
    rw [Category.assoc, ← Functor.map_comp, ← op_comp]
    simp [← h1, ← h2, reassoc_of% this]

@[simp]
lemma multifork_ι (A : S.Arrow) :
    (multifork R S P s gen).ι A = s.ι (gen.arrow A) ≫ P.map (gen.l A.f A.hf).op :=
  rfl

@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.Limits.Multifork.IsLimit.lift_ι
    {C : Type*} [Category C] {J : MulticospanShape} {I : MulticospanIndex J C}
    (K L : Multifork I) (hK : IsLimit K) (a : J.L) :
    hK.lift L ≫ K.ι a = L.ι a :=
  IsLimit.fac _ _ _

@[simp]
lemma _root_.CategoryTheory.Limits.Multifork.ofι_ι
    {C : Type*} [Category C] {J : MulticospanShape} (I : MulticospanIndex J C) (P : C)
    (ι : (a : J.L) → P ⟶ I.left a)
    (w : ∀ (b : J.R), ι (J.fst b) ≫ I.fst b = ι (J.snd b) ≫ I.snd b) :
    (Multifork.ofι I P ι w).ι = ι :=
  rfl

noncomputable
def isLimitMultiFork : IsLimit (multifork R S P s gen) := by
  refine Multifork.IsLimit.mk _ ?_ ?_ ?_
  · intro E
    let E' : Multifork (R.index P) := by
      refine Multifork.ofι _ E.pt (fun a ↦ ?_) (fun b ↦ ?_)
      · exact E.ι ⟨a.Y, a.f, hle _ a.hf⟩
      · letI rel : S.Relation :=
          { fst := ⟨b.1.Y, b.1.f, hle _ b.1.hf⟩
            snd := ⟨b.2.Y, b.2.f, hle _ b.2.hf⟩
            r := ⟨pullback b.1.f b.2.f, pullback.fst _ _, pullback.snd _ _, pullback.condition⟩ }
        exact E.condition rel
    exact hs.lift E'
  · intro E A
    let rel : S.Relation :=
      { fst := A
        snd := ⟨gen.obj A.f A.hf, gen.r A.f A.hf, hle _ (gen.r_mem A.f A.hf)⟩
        r := ⟨A.Y, 𝟙 _, gen.l A.f A.hf, by simp⟩ }
    simpa [rel] using (E.condition rel).symm
  · intro E m hm
    simp only [multifork_pt, Cover.shape_L]
    apply Multifork.IsLimit.hom_ext hs
    intro a
    simp only [GrothendieckTopology.Cover.shape_L, GrothendieckTopology.Cover.index_left,
      multifork_pt, multifork_ι, Cover.index_left, Presieve.GenerateStruct.arrow_Y] at hm
    simp only [Cover.index_left, Multifork.IsLimit.lift_ι, Multifork.ofι_ι,
      ← hm ⟨a.Y, a.f, hle _ a.hf⟩]
    have := s.condition ⟨a, gen.arrow ⟨a.Y, a.f, hle _ a.hf⟩⟩
    simp only [Cover.index_right, Presieve.GenerateStruct.arrow_Y, Presieve.GenerateStruct.arrow_f,
      Cover.shape_fst, Cover.index_left, Cover.index_fst, Cover.shape_snd, Cover.index_snd] at this
    have h : _ ≫ pullback.snd a.f (gen.r a.f (hle _ a.hf)) = _ :=
      pullback.lift_snd (𝟙 _) (gen.l a.f (hle _ a.hf)) (by simp)
    rw [← h, op_comp, P.map_comp, ← reassoc_of% this, ← P.map_comp, ← op_comp]
    simp

lemma hasMultiequalizer_index_of_generate_eq (h : Sieve.generate R.1 = S)
    [HasMultiequalizer (R.index P)] : HasMultiequalizer (S.index P) := by
  obtain ⟨gen⟩ := R.1.nonempty_generateStruct_of_le S (h ▸ le_rfl)
  exact ⟨⟨multifork R S P (Multiequalizer.multifork (R.index P)) gen,
    isLimitMultiFork R S (by rw [← Sieve.generate_le_iff, h]) P _ (limit.isLimit _) gen⟩⟩

end Pretopology

namespace GrothendieckTopology

variable (J : GrothendieckTopology C)
variable {S T : J.Cover X}
variable {D : Type*} [Category D] (P : Cᵒᵖ ⥤ D)
variable (E : Multifork (S.index P)) (hE : IsLimit E)

-- this does not work
def multifork (hle : S ≤ T) : Multifork (T.index P) := by
  refine Multifork.ofι _ E.pt ?_ ?_
  · intro (A : T.Arrow)
    sorry
  · sorry

end GrothendieckTopology

/-- Alternative constructor when the def-eq needed for `Presieve.ofArrows.mk` is hard to obtain. -/
lemma Presieve.ofArrows.mk' {X : C} {ι : Type*} {Y : ι → C} {f : ∀ i, Y i ⟶ X} {Z : C} {g : Z ⟶ X}
    (i : ι) (h : Z = Y i) (heq : g = eqToHom h ≫ f i) :
    Presieve.ofArrows Y f g := by
  subst h heq
  simp only [eqToHom_refl, Category.id_comp]
  use i

@[simps!]
def Presieve.functorPullbackFunctor {D : Type*} [Category D] (F : C ⥤ D) (X : C) :
    Presieve (F.obj X) ⥤ Presieve X :=
  (Presieve.monotone_functorPullback F X).functor

variable [HasPullbacks C] (J : Pretopology C)

def Pretopology.generateCover (X : C) (R : J X) : (J.toGrothendieck C).Cover X :=
  ⟨Sieve.generate R, by simp⟩

lemma Pretopology.monotone_generateCover (X : C) : Monotone (J.generateCover X) :=
  fun _ _ ↦ Sieve.generate_mono

/-- The biggest presieve in `J` generating `S`. -/
def Pretopology.generator {X : C} (S : Sieve X) : Presieve X :=
  ⨆ R ∈ J X, ⨆ (_ : R ≤ S), R

lemma Pretopology.generator_ofGrothendieck (J : GrothendieckTopology C) {X : C} (S : Sieve X)
    (hS : S ∈ J X) :
    (ofGrothendieck C J).generator S = S := by
  refine le_antisymm ?_ ?_
  · simp [generator]
  · rw [generator]
    apply le_iSup_of_le S.arrows
    apply le_iSup_of_le
    · apply le_iSup_of_le le_rfl
      exact le_rfl
    rwa [mem_ofGrothendieck, Sieve.generate_sieve]

end CategoryTheory

@[simps]
def Scheme.zariskiPretopologyToSetOpens (X : Scheme.{u}) :
    Scheme.zariskiPretopology X ⥤ Set (Opens X) where
  obj R :=
    { U | ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (hf : R.1 f), Set.range f.base = U.1 }
  map {R₁ R₂} g := homOfLE <| by
    rintro U ⟨Y, f, hf, hU⟩
    exact ⟨Y, f, g.1.1 _ hf, hU⟩

namespace AlgebraicGeometry

instance {S : Scheme.{u}} (X : MorphismProperty.Over @IsOpenImmersion ⊤ S) :
    IsOpenImmersion X.hom := X.prop

noncomputable
def Scheme.overIsOpenImmersionEquiv (X : Scheme.{u}) :
    MorphismProperty.Over @IsOpenImmersion ⊤ X ≌ X.Opens where
  functor.obj U := U.hom.opensRange
  functor.map {U V} f := homOfLE <| by
    have : U.hom = f.left ≫ V.hom := by simp
    simp_rw [this]
    change Set.range _ ⊆ _
    rw [Scheme.comp_base]
    simp [Set.range_comp]
  inverse.obj U := .mk ⊤ U.ι inferInstance
  inverse.map {U V} f :=
    MorphismProperty.Over.homMk (X.homOfLE f.1.1) (by simp)
  unitIso := NatIso.ofComponents (fun U ↦ MorphismProperty.Over.isoMk
      (IsOpenImmersion.isoOfRangeEq U.hom U.hom.opensRange.ι (by simp))) <| fun {U V} f ↦ by
    ext
    rw [← cancel_mono V.hom.opensRange.ι]
    simp
  counitIso := NatIso.ofComponents (fun U ↦ eqToIso (by simp))

instance (X : Scheme.{u}) :
    EssentiallySmall.{u} (MorphismProperty.Over @IsOpenImmersion ⊤ X) := by
  constructor
  use X.Opens, inferInstance
  exact ⟨X.overIsOpenImmersionEquiv⟩

instance Scheme.Cover.overSelf {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}} (𝒰 : S.Cover P) :
    𝒰.Over S where
  over j := ⟨𝒰.map j⟩
  isOver_map j := by
    rw [Scheme.Hom.isOver_iff, CategoryTheory.over_def, Category.comp_id]
    rfl

@[simp]
lemma Scheme.Cover.overSelf_over {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}} {𝒰 : S.Cover P}
    (j : 𝒰.J) :
    𝒰.obj j ↘ S = 𝒰.map j := rfl

section

variable (P Q : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  [Q.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [Q.IsMultiplicative]

@[simps!]
def Scheme.toSmallPretopology (X : Scheme.{u}) :
    Scheme.pretopology P X ↪o X.smallPretopology P P (.mk _ _ (P.id_mem X)) := by
  refine RelEmbedding.ofMapRelIff (fun R ↦ ?_) ?_
  · refine ⟨fun Y f ↦ R.1 f.left, ?_⟩
    obtain ⟨-, 𝒰, rfl⟩ := R
    refine ⟨𝒰, inferInstance, fun j ↦ 𝒰.map_prop j, ?_⟩
    · apply le_antisymm
      · intro Y g (hg : Presieve.ofArrows 𝒰.obj 𝒰.map g.left)
        obtain ⟨i, h, hg⟩ := Presieve.ofArrows_surj _ _ hg
        let g' : (𝒰.obj i).asOverProp X (𝒰.map_prop i) ⟶
          .mk ⊤ (𝟙 X) (P.id_mem X) := Scheme.Hom.asOverProp (P := P) (𝒰.map i) X
        have : g = eqToHom (by ext; exact h.symm; simp [← Over.w g.hom, hg]) ≫ g' := by
          ext; simp [hg, g']
        exact .mk' i _ this
      · rintro - - ⟨i⟩
        use i
  · rintro ⟨R₁, 𝒰, rfl⟩ ⟨R₂, 𝒱, rfl⟩
    refine ⟨fun h ↦ ?_, fun h Y g hg ↦ h _ hg⟩
    rintro - - ⟨i⟩
    let g : (𝒰.obj i).asOverProp X (𝒰.map_prop i) ⟶ .mk ⊤ (𝟙 X) (P.id_mem X) :=
      (𝒰.map i).asOverProp X
    obtain ⟨j, h, hg⟩ :=
      Presieve.ofArrows_surj _ _ <| @h ((𝒰.obj i).asOverProp X (𝒰.map_prop i)) g ⟨i⟩
    exact .mk' j _ hg

def Scheme.coverPretopologyEmb (X : Scheme.{u}) :
    (Scheme.pretopology P).Cover X ↪o (X.smallPretopology P P).Cover (.mk _ _ (P.id_mem X)) where
  __ := X.toSmallPretopology P
  map_rel_iff' := by
    rintro ⟨R, 𝒰, rfl⟩ ⟨S, 𝒱, rfl⟩
    refine ⟨fun hle ↦ ?_, fun hle ↦ ?_⟩
    · rintro - - ⟨i⟩
      let g : (𝒰.obj i).asOverProp X (𝒰.map_prop i) ⟶ .mk ⊤ (𝟙 X) (P.id_mem X) :=
        (𝒰.map i).asOverProp X
      obtain ⟨Z, f, (h : Presieve.ofArrows _ 𝒱.map f.left), u, hg⟩ :=
        @hle ((𝒰.obj i).asOverProp X (𝒰.map_prop i)) g ⟨i⟩
      refine ⟨Z.left, f.left, ?_, u.left, congr($(hg).left)⟩
      obtain ⟨j, h, hg⟩ := Presieve.ofArrows_surj _ _ h
      exact .mk' j _ hg
    · rintro Y f hf
      obtain ⟨Z, g, hg, u, hu⟩ := hle _ hf
      obtain ⟨i, h, hf⟩ := Presieve.ofArrows_surj _ _ hf
      obtain ⟨j, h2, hg⟩ := Presieve.ofArrows_surj _ _ hg
      use .mk _ g (by rw [hg, P.cancel_left_of_respectsIso]; exact 𝒱.map_prop j)
      use MorphismProperty.Over.homMk g
      refine ⟨.mk' j _ hg, MorphismProperty.Over.homMk u (hu.trans ?_), by ext; simpa⟩
      simpa using f.w

/-- If the small sites associated to `P` are essentially small, the covers of the pretopology
associated to `P` are essentially small for every `X : Scheme`. -/
instance essentiallySmall_cover_pretopology
    [∀ X, EssentiallySmall.{u} (MorphismProperty.Over P ⊤ X)] (X : Scheme.{u}) :
    EssentiallySmall.{u} ((Scheme.pretopology P).Cover X) := by
  let F' : (Scheme.pretopology P).Cover X ⥤ (X.smallPretopology P P).Cover (.mk _ _ (P.id_mem X)) :=
    (X.coverPretopologyEmb P).monotone.functor
  exact essentiallySmall_of_fully_faithful.{u} F'

end

/-- The Zariski covers of any scheme `X` are essentially small. -/
instance (X : Scheme.{u}) : EssentiallySmall.{u} (Scheme.zariskiPretopology.Cover X) :=
  essentiallySmall_cover_pretopology @IsOpenImmersion X

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance : HasSheafify Scheme.zariskiTopology.{u} (Type u) := by
  --have (P : Schemeᵒᵖ ⥤ Type u) (X : Scheme) (S : Scheme.zariskiTopology.Cover X) :
  --    Limits.HasMultiequalizer (S.index P) :=
  --  sorry
  --have : ∀ (X : Scheme), HasColimitsOfShape (Scheme.zariskiTopology.Cover X)ᵒᵖ (Type u) :=
  --  sorry
  --have : ∀ (X : Scheme), HasColimitsOfShape (↑(Scheme.zariskiPretopology.coverings X))ᵒᵖ (Type u) :=
  --  sorry
  --apply hasSheafify_of_initial.{u} Scheme.zariskiTopology.{u} _
  --  fun X ↦ Scheme.zariskiPretopology.toCover X
  sorry

end AlgebraicGeometry
