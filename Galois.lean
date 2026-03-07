import Mathlib.FieldTheory.Galois
import Mathlib.FieldTheory.IntermediateField
import Mathlib.FieldTheory.Minpoly.Basic

-- Πειραματισμοί

variable (K L : Type _) [Field K] [Field L] [Algebra K L]

-- Έλεγχος των ορισμών
#check IsAlgebraic
#check IntermediateField

/-- Ένα στοιχείο είναι αλγεβρικό αν το minpoly δεν είναι μηδέν. 
    Δοκιμάζω να το αποδείξω με διαφορετικές τακτικές. -/
lemma algebraic_element_test (x : L) (h : IsAlgebraic K x) : 
    minpoly K x ≠ 0 := by
  -- Δοκιμάζω με την άμεση ιδιότητα του ελάχιστου πολυωνύμου
  exact minpoly.ne_zero h

/-- Ορισμός του "σταθερού σώματος" χειροκίνητα -/
def my_fixed_field (G : Subgroup (L ≃ₐ[K] L)) : Set L :=
  { x : L | ∀ g ∈ G, g x = x }

-- Προσπάθεια να δείξω ότι το my_fixed_field περιέχει το K
-- Εδώ χρησιμοποιώ το term mode για να δείξω ότι κατανοώ το coercion
example (G : Subgroup (L ≃ₐ[K] L)) (k : K) : 
    algebraMap K L k ∈ my_fixed_field K L G := by
  intro g hg
  -- Οι αυτομορφισμοί του K-algebra αφήνουν το K αναλλοίωτο εξ ορισμού
  rw [AlgEquiv.commutes]

/- 
  Galois Group: Δοκιμές με την ομάδα αυτομορφισμών 
-/

/-- Το μέγεθος του Galois Group για πεπερασμένη επέκταση. 
    Εδώ αφήνω sorry γιατί θέλει αρκετά lemmas για να κλείσει. -/
theorem galois_card_fixed_field [FiniteDimensional K L] [IsGalois K L] :
    Fintype.card (L ≃ₐ[K] L) = FiniteDimensional.finrank K L := by
  -- TODO: Να χρησιμοποιήσω το `IsGalois.card_aut_eq_finrank`
  sorry

-- Δοκιμάζω αν η σύνθεση αυτομορφισμών δουλεύει όπως περιμένω
example (f g : L ≃ₐ[K] L) (x : L) : (f * g) x = f (g x) := rfl

/- 
  Section: Θεωρία Συνόλων & Επεκτάσεις
  Δοκιμάζω να ορίσω ένα IntermediateField από ένα μόνο στοιχείο (Adjunction)
-/

variable (α : L)

def simple_extension := adjoin K {α}

-- Πώς μπορώ να δείξω ότι το α ανήκει στην επέκταση;
example : α ∈ adjoin K {α} := by
  apply subset_adjoin
  simp

-- Δοκιμή: Αν το α είναι στο K, τότε το adjoin K {α} είναι το ίδιο το K;
example (h : ∃ k : K, algebraMap K L k = α) : adjoin K {α} = ⊥ := by
  rcases h with ⟨k, rfl⟩
  apply adjoin_le_iff.mpr
  simp
  -- Το ⊥ αντιπροσωπεύει το βασικό σώμα K
  sorry -- θέλει λίγο ψάξιμο με τα lattice properties

-- #check για επαλήθευση τύπων
#check (⊥ : IntermediateField K L)
#check (⊤ : IntermediateField K L)
