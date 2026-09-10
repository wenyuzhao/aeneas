import Lean
import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Notations

namespace Aeneas

open Lean Elab Term Meta
open Lean.Parser.Term Command

namespace Std

/-- This typeclass models the discriminant reads which sometimes happen in Rust -/
class Discriminant (α : Type u) (β : outParam (Type v)) where
  read_discriminant : α → β

export Discriminant (read_discriminant)

end Std

namespace Discriminant

initialize registerTraceClass `Discriminant

inductive ScalarTy where
| U8 | U16 | U32 | U64 | U128 | Usize
| I8 | I16 | I32 | I64 | I128 | Isize

def mkScalarValue (ty : ScalarTy) (val : Int) : TermElabM Term := do
  let value : Term ←
    if val ≥ 0 then
      let n := Syntax.mkNumLit (toString val.toNat)
      `($n)
    else
      let n := Syntax.mkNumLit (toString (-val).toNat)
      `((-$n))
  match ty with
  | .U8 => `($(value)#u8)
  | .U16 => `($(value)#u16)
  | .U32 => `($(value)#u32)
  | .U64 => `($(value)#u64)
  | .U128 => `($(value)#u128)
  | .Usize => `($(value)#usize)
  | .I8 => `($(value)#i8)
  | .I16 => `($(value)#i16)
  | .I32 => `($(value)#i32)
  | .I64 => `($(value)#i64)
  | .I128 => `($(value)#i128)
  | .Isize => `($(value)#isize)

def mkScalarTy (ty : ScalarTy) : TermElabM Term := do
  match ty with
  | .U8 => `(_root_.Aeneas.Std.U8)
  | .U16 => `(_root_.Aeneas.Std.U16)
  | .U32 => `(_root_.Aeneas.Std.U32)
  | .U64 => `(_root_.Aeneas.Std.U64)
  | .U128 => `(_root_.Aeneas.Std.U128)
  | .Usize => `(_root_.Aeneas.Std.Usize)
  | .I8 => `(_root_.Aeneas.Std.I8)
  | .I16 => `(_root_.Aeneas.Std.I16)
  | .I32 => `(_root_.Aeneas.Std.I32)
  | .I64 => `(_root_.Aeneas.Std.I64)
  | .I128 => `(_root_.Aeneas.Std.I128)
  | .Isize => `(_root_.Aeneas.Std.Isize)

/-- Auxiliary helper for `generateReadDiscriminant`.

This function is adapted from `Lean.Elab.Deriving.BEq`.
-/
def generateReadDiscriminantCmds (declName : Name) (ty : ScalarTy) (discrValues : Option (List Int)) :
  TermElabM (List Syntax) := do
  -- Lookup the declaration, which should be an inductive
  let env ← getEnv
  let some decl := env.findAsync? declName
    | throwError "Could not find declaration {declName}"
  let indVal ← match decl.constInfo.get with
    | .inductInfo const => pure const
    | _ => throwError "Declaration is not an inductive: {declName}"

  /- We try to piggyback as much as possible on the utilities introducing for `deriving`.
  In particular, the following helper generates the parameter names and binders we need.

  The only caveat is that it introduces typeclass instances for the generic types.
  For instance, if we give it type `inductive Foo (α β : Type)` it will generate binders:
  `{α β : Type} [Discriminant α] [Discriminant β] (x : Foo α β)`
  Because of this, we need to update the binders to drop `[Discriminant α]` and `[Discriminant β]`
  (TODO: this is rather inelegant).
  -/
  let header ← Lean.Elab.Deriving.mkHeader ``Std.Discriminant 2 indVal
  trace[Discriminant] "numParams: {indVal.numParams}"
  let header : Deriving.Header :=
    let binders := header.binders
    let binders := binders.extract 0 indVal.numParams ++ [binders[binders.size - 2]!]
    { header with binders }

  -- Generate the value of the discriminant for each variant
  let discrValues ← do
    match discrValues with
    | none => pure (indVal.ctors.mapIdx (fun n _ => Int.ofNat n))
    | some values =>
      if values.length ≠ indVal.ctors.length then
        throwError "Invalid number of values provided ({discrValues}): got {values.length}, expected {indVal.ctors.length}"
      pure values

  -- Generate the match branches
  let alts : List (TSyntax `Lean.Parser.Term.matchAltExpr) ←
    indVal.ctors.mapIdxM fun i ctorName => do
    let ctorInfo ← getConstInfoCtor ctorName
    let value ← mkScalarValue ty discrValues[i]!
    let alt ← do
      -- Generate one `_` pattern for each index then for each field
      let mut patterns := #[]
      for _ in 0...(indVal.numIndices + ctorInfo.numFields) do
        patterns := patterns.push (← `(_))
      let pat ← `($(mkIdent ctorName):ident $patterns:term*)
      `(matchAltExpr| | $pat => $value:term)
    pure alt
  let alts := alts.toArray

  -- Generate the match itself
  let varName := header.targetNames[0]!
  let discr : TSyntax ``Parser.Term.matchDiscr ←
    `(Parser.Term.matchDiscr| $(mkIdent varName):term)
  let discrs : Array (TSyntax `Lean.Parser.Term.matchDiscr) := #[discr]
  let body ← `(match $[$discrs],* with $alts:matchAlt*)

  -- Generate the syntax for function definition
  let ty ← mkScalarTy ty
  let auxFunName := Name.mkStr declName "read_discriminant"
  let binders := header.binders
  let defStx ← `(def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $ty := $body:term)

  -- Generate the syntax for the instance
  let binders := binders.extract 0 indVal.numParams
  let args := header.argNames.map mkIdent
  let instStx ← `(instance $binders:bracketedBinder* : Aeneas.Std.Discriminant ($header.targetType) ($ty) where
      read_discriminant := @$(mkIdent auxFunName):ident $args*)

  --
  pure [defStx, instStx]

/-- Given an inductive declaration name and an optional list of values, generate an instance
of `Std.Discriminant`. If the list of values is not provided, we use values `0`, `1`, etc. -/
def generateReadDiscriminant (declName : Name) (ty : ScalarTy) (discrValues : Option (List Int)) :
  CommandElabM Unit := do
  let cmds ← liftTermElabM (generateReadDiscriminantCmds declName ty discrValues)
  cmds.forM elabCommand

syntax discrVal := "-"? num
syntax (name := readDiscriminant) "discriminant" ident ("["discrVal,*"]")? : attr

def elabTypeToken (stx : Syntax) : AttrM ScalarTy :=
  match stx.getId with
  | `u8 => pure ScalarTy.U8
  | `u16 => pure ScalarTy.U16
  | `u32 => pure ScalarTy.U32
  | `u64 => pure ScalarTy.U64
  | `u128 => pure ScalarTy.U128
  | `usize => pure ScalarTy.Usize
  | `i8 => pure ScalarTy.I8
  | `i16 => pure ScalarTy.I16
  | `i32 => pure ScalarTy.I32
  | `i64 => pure ScalarTy.I64
  | `i128 => pure ScalarTy.I128
  | `isize => pure ScalarTy.Isize
  | _ => throwUnsupportedSyntax

def elabDiscrVal (stx : Syntax) : AttrM Int :=
  match stx with
  | `(discrVal| $n:num) => pure (Int.ofNat n.getNat)
  | `(discrVal| -$n:num) => pure (- Int.ofNat n.getNat)
  | _ => throwUnsupportedSyntax

def elabReadDiscriminantAttribute (stx : Syntax) : AttrM (ScalarTy × Option (List Int)) :=
  withRef stx do
    match stx with
    | `(attr| discriminant $ty) => do
      trace[Discriminant] "Elaborating discriminant attribute without values"
      pure (← elabTypeToken ty, none)
    | `(attr| discriminant $ty [$x,*]) => do
      trace[Discriminant] "Elaborating discriminant attribute with values: {x.getElems}"
      let values ← x.getElems.toList.mapM elabDiscrVal
      pure (← elabTypeToken ty, some values)
    | _ => throwUnsupportedSyntax

initialize discriminantAttribute : AttributeImpl ← do
  let attrImpl : AttributeImpl := {
    name := `readDiscriminant
    descr := "Generates an instance of `Std.Discriminant` for the given inductive"
    add := fun declName stx attrKind => do
      -- Elaborate the attribute
      let (ty, values) ← elabReadDiscriminantAttribute stx
      -- Generate the definitions
      liftCommandElabM (generateReadDiscriminant declName ty values)
  }
  registerBuiltinAttribute attrImpl
  pure attrImpl

namespace Test

  open Std

  mutual

  inductive Foo (α β : Type) where
  | Bar (y : Nat)
  | Baz (x : α) (y : β)

  inductive Foo1 (α β : Type) where
  | Variant1 | Variant2

  end

  inductive Foo2 where
  | Variant1
  | Variant2

  inductive Foo3 where
  | Variant1
  | Variant2

  inductive Foo4 where
  | CoarseSlower | MediumSlower | FineSlower | NoChange | FineFaster | MediumFaster | CoarseFaster

  inductive Foo5 where
  | Min | NegOne | Zero | One | Max

  inductive Foo6 where
  | Neg | Zero | Pos

  #eval generateReadDiscriminant ``Foo .U8 (some [3, 4])
  #eval generateReadDiscriminant ``Foo1 .I8 none
  #eval generateReadDiscriminant ``Foo2 .I16 none
  #eval generateReadDiscriminant ``Foo3 .Isize (some [3, 4])
  #eval generateReadDiscriminant ``Foo4 .Isize (some [-3, -2, -1, 0, 1, 2, 3])
  #eval generateReadDiscriminant ``Foo5 .I8 (some [-128, -1, 0, 1, 127])
  #eval generateReadDiscriminant ``Foo6 .I32 (some [-100, 0, 100])

  #assert read_discriminant Foo2.Variant1 = 0#i16
  #assert read_discriminant Foo3.Variant1 = 3#isize
  #assert read_discriminant Foo3.Variant2 = 4#isize
  #assert read_discriminant Foo4.CoarseSlower = (-3)#isize
  #assert read_discriminant Foo4.MediumSlower = (-2)#isize
  #assert read_discriminant Foo4.FineSlower = (-1)#isize
  #assert read_discriminant Foo4.NoChange = 0#isize
  #assert read_discriminant Foo4.FineFaster = 1#isize
  #assert read_discriminant Foo4.MediumFaster = 2#isize
  #assert read_discriminant Foo4.CoarseFaster = 3#isize
  #assert read_discriminant Foo5.Min = (-128)#i8
  #assert read_discriminant Foo5.NegOne = (-1)#i8
  #assert read_discriminant Foo5.Zero = 0#i8
  #assert read_discriminant Foo5.One = 1#i8
  #assert read_discriminant Foo5.Max = 127#i8
  #assert read_discriminant Foo6.Neg = (-100)#i32
  #assert read_discriminant Foo6.Zero = 0#i32
  #assert read_discriminant Foo6.Pos = 100#i32

end Test

end Discriminant

end Aeneas
