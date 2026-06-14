import Lean
import Lean4Less.PExpr

open Lean

instance : Coe LocalDecl FVarId where
  coe decl := decl.fvarId

instance : ToString FVarIdSet where
toString s := toString $ s.toArray.map (·.1)

namespace Lean4Less

/--
  Optimized version of Lean.Expr.containsFVar, assuming no bound vars in `e`.
-/
def _root_.Lean.Expr.containsFVar' (e : Expr) (fv : FVarId) : Bool :=
  (e.abstract #[.fvar fv]).hasLooseBVars

def PExpr.containsFVar' (e : PExpr) (fv : LocalDecl) : Bool := -- optimized version of Lean.Expr.containsFVar
  e.toExpr.containsFVar' fv.fvarId

instance : Hashable LocalDecl where
hash l := hash (l.toExpr, l.type)

instance : BEq LocalDecl where
beq l l' := (l.toExpr, l.type) == (l'.toExpr, l'.type)

structure EContext where
  dbg : Bool := false -- (for debugging purposes)
  rev : Bool := false
  ctorStack : Array (Name × Array Name) := #[]
  reversedFvars : Std.HashSet FVarId := {}

structure LocalDeclE where
(index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr) (usedLets : FVarIdSet) (value : EContext → Expr)
deriving Inhabited

inductive LocalDecl' where
| e : LocalDeclE → LocalDecl'
| l : LocalDecl → LocalDecl'
deriving Inhabited

def LocalDeclE.toLocalDecl (l : LocalDeclE) : LocalDecl := 
.ldecl l.index l.fvarId l.userName l.type (l.value {}) false default -- TODO investigate use of `LocalDeclKind` field

-- FIXME should I really be doing this?
instance : Coe (Array LocalDeclE) FVarIdSet where
coe ls := ls.foldl (init := default) fun acc l => acc.union l.usedLets

/--
Tracks fvars for an equality in both directions (useful when reversing equalities).
-/
structure FVarDataE where
A : PExpr
B : PExpr
a : PExpr
b : PExpr
u : Level
aEqb : LocalDecl
bEqa : LocalDecl
usedLets : FVarIdSet := FVarIdSet.insert default aEqb
deriving Inhabited

structure LVarDataE where
A : PExpr
B : PExpr
a : PExpr
b : PExpr
u : Level
v : FVarId
usedLets : FVarIdSet := FVarIdSet.insert default v
deriving Inhabited

structure FVarData where
aEqb : LocalDecl
bEqa : LocalDecl
lets : Array LocalDeclE
usedLets : FVarIdSet := lets
deriving Inhabited

structure SorryData where
u    : Level
A    : PExpr
a    : PExpr
B    : PExpr
b    : PExpr
deriving Inhabited, Hashable, BEq

/-- A proof of `HEq a b` (both `: A`) witnessing the elimination of *unit-eta*: when the
    kernel would use `a ≡ b` because they inhabit a unit type (single 0-field constructor),
    we record an explicit proof instead. `proof` is the inlined `@I.rec`-based term built in
    `isDefEqUnitLike`. -/
structure UnitEtaData where
u     : Level
A     : PExpr
a     : PExpr
b     : PExpr
proof : PExpr
deriving Inhabited, Hashable, BEq

structure CastData (EExpr : Type) where
u    : Level
A    : PExpr
B    : PExpr
e    : PExpr
p    : EExpr
deriving Inhabited, Hashable, BEq



structure LamABData (EExpr : Type) where
B      : PExpr
b      : LocalDecl
blets  : Array LocalDeclE
vaEqb  : FVarData
hAB    : EExpr × FVarIdSet
usedLets : FVarIdSet := hAB.2.union (blets : FVarIdSet) |>.union vaEqb.usedLets

structure LamUVData where
V   : PExpr × LocalDecl
deriving Hashable, BEq

inductive LamDataExtra (EExpr : Type) where
| ABUV : LamABData EExpr → LamUVData → LamDataExtra EExpr
| UV   : LamUVData → LamDataExtra EExpr
| none : LamDataExtra EExpr
with
@[computed_field]
usedLets : (EExpr : Type) → LamDataExtra EExpr → FVarIdSet
| _, .ABUV d .. => d.usedLets
| _, _ => default
deriving Inhabited

structure LamData (EExpr : Type) where
u      : Level
v      : Level
A      : PExpr
U      : PExpr × LocalDecl
f      : PExpr
a      : LocalDecl
alets  : Array LocalDeclE
g      : PExpr
faEqgx : EExpr × FVarIdSet
extra  : LamDataExtra EExpr := .none
usedLets := faEqgx.2.union extra.usedLets |>.union (alets : FVarIdSet)
deriving Inhabited


structure ForallUVData (EExpr : Type) where
V      : PExpr × LocalDecl
UaEqVx : EExpr × FVarIdSet
usedLets := UaEqVx.2
deriving Inhabited

structure ForallABUVData (EExpr : Type) where
B      : PExpr
b      : LocalDecl
blets  : Array LocalDeclE
vaEqb  : FVarData
hAB    : EExpr × FVarIdSet
V      : PExpr × LocalDecl
UaEqVx : EExpr × FVarIdSet
usedLets := hAB.2.union UaEqVx.2 |>.union (blets : FVarIdSet) |>.union vaEqb.usedLets

structure ForallABData (EExpr : Type) where
B      : PExpr
b      : LocalDecl
blets  : Array LocalDeclE
vaEqb  : FVarData
hAB    : EExpr × FVarIdSet
usedLets := hAB.2.union (blets : FVarIdSet) |>.union vaEqb.usedLets

-- structure ForallABUVAppData (EExpr : Type) :=
-- b      : LocalDecl
-- vaEqb  : FVarData
-- V      : PExpr × LocalDecl
-- UaEqVx : EExpr
-- deriving Hashable, BEq

-- structure ForallABAppData (EExpr : Type) :=
-- b      : LocalDecl
-- vaEqb  : FVarData
-- deriving Hashable, BEq

inductive ForallDataExtra (EExpr : Type) where
| ABUV   : ForallABUVData EExpr → ForallDataExtra EExpr
| UV     : ForallUVData EExpr → ForallDataExtra EExpr
| AB     : ForallABData EExpr → ForallDataExtra EExpr
with
@[computed_field]
usedLets : (EExpr : Type) → ForallDataExtra EExpr → FVarIdSet
| _, .ABUV d ..
| _, .UV d ..
| _, .AB d .. => d.usedLets
deriving Inhabited

structure ForallData (EExpr : Type) where
u      : Level
v      : Level
A      : PExpr
a      : LocalDecl
alets  : Array LocalDeclE
U      : PExpr × LocalDecl
extra  : ForallDataExtra EExpr
usedLets : FVarIdSet := .union extra.usedLets (alets : FVarIdSet)
deriving Inhabited



structure HUVDataExtra where
b      : LocalDecl
blets  : Array LocalDeclE
vaEqb  : FVarData
usedLets : FVarIdSet := .union (blets : FVarIdSet) vaEqb.usedLets
deriving Inhabited

structure HUVData (EExpr : Type) where
a      : LocalDecl
alets  : Array LocalDeclE
UaEqVb : EExpr × FVarIdSet
extra  : Option HUVDataExtra
usedLets := UaEqVb.2.union (alets : FVarIdSet) |>.union $ (extra.map fun d => d.usedLets).getD default
deriving Inhabited



structure AppDataNone (EExpr : Type) where
g    : PExpr
fEqg : EExpr × FVarIdSet
b    : PExpr
aEqb : EExpr × FVarIdSet
usedLets := fEqg.2.union aEqb.2
deriving Inhabited

structure AppDataArg (EExpr : Type) where
b    : PExpr
aEqb : EExpr × FVarIdSet
usedLets := aEqb.2
deriving Inhabited

structure AppDataFun (EExpr : Type) where
g    : PExpr
fEqg : EExpr × FVarIdSet
usedLets := fEqg.2
deriving Inhabited

structure AppDataAB (EExpr : Type) where
B    : PExpr
hAB  : EExpr × FVarIdSet
g    : PExpr
fEqg : EExpr × FVarIdSet
b    : PExpr
aEqb : EExpr × FVarIdSet
usedLets := hAB.2.union fEqg.2 |>.union aEqb.2
deriving Inhabited

structure AppDataUV (EExpr : Type) where
V    : PExpr × LocalDecl
hUV  : HUVData EExpr
g    : PExpr
fEqg : EExpr × FVarIdSet
b    : PExpr
aEqb : EExpr × FVarIdSet
usedLets := fEqg.2.union aEqb.2 |>.union hUV.usedLets
deriving Inhabited

structure AppDataUVFun (EExpr : Type) where
V    : PExpr × LocalDecl
hUV  : HUVData EExpr
g    : PExpr
fEqg : EExpr × FVarIdSet
usedLets := fEqg.2.union hUV.usedLets
deriving Inhabited

structure AppDataABUV (EExpr : Type) where
B    : PExpr
hAB  : EExpr × FVarIdSet
V    : PExpr × LocalDecl
hUV  : HUVData EExpr
g    : PExpr
fEqg : EExpr × FVarIdSet
b    : PExpr
aEqb : EExpr × FVarIdSet
usedLets := fEqg.2.union hUV.usedLets |>.union aEqb.2 |>.union hAB.2
deriving Inhabited

inductive AppDataExtra (EExpr : Type) where
| none  : AppDataNone EExpr → AppDataExtra EExpr
| Fun   : AppDataFun EExpr → AppDataExtra EExpr
| Arg   : AppDataArg EExpr → AppDataExtra EExpr
| UV    : AppDataUV EExpr → AppDataExtra EExpr
| UVFun : AppDataUVFun EExpr → AppDataExtra EExpr
| AB    : AppDataAB EExpr → AppDataExtra EExpr
| ABUV  : AppDataABUV EExpr → AppDataExtra EExpr
with
@[computed_field]
usedLets : (EExpr : Type) → AppDataExtra EExpr → FVarIdSet
| _, .none  d
| _, .Fun   d
| _, .Arg   d
| _, .UV    d
| _, .UVFun d
| _, .AB    d
| _, .ABUV  d => d.usedLets
deriving Inhabited

structure AppData (EExpr : Type) where
u     : Level
v     : Level
A     : PExpr
U     : PExpr × LocalDecl -- TODO mae fvar arg optional
f     : PExpr
a     : PExpr
extra : AppDataExtra EExpr
usedLets' : FVarIdSet := default
usedLets := usedLets'.union extra.usedLets
deriving Inhabited



structure TransData (EExpr : Type) where
u     : Level
A     : PExpr
B     : PExpr
C     : PExpr
a     : PExpr
b     : PExpr
c     : PExpr
aEqb  : EExpr × FVarIdSet
bEqc  : EExpr × FVarIdSet
usedLets := aEqb.2.union bEqc.2
deriving Inhabited



-- structure SymmData (EExpr : Type) where
-- u     : Level
-- A     : PExpr
-- B     : PExpr
-- a     : PExpr
-- b     : PExpr
-- aEqb  : EExpr
-- deriving Inhabited, Hashable, BEq
--


structure ReflData where
u     : Level
A     : PExpr
a     : PExpr
deriving Inhabited



structure PIDataHEq (EExpr : Type) where
Q    : PExpr
hPQ  : EExpr × FVarIdSet
usedLets := hPQ.2
deriving Inhabited

inductive PIDataExtra (EExpr : Type) where
| none 
| HEq   : PIDataHEq EExpr → PIDataExtra EExpr
with
@[computed_field]
usedLets : (EExpr : Type) → PIDataExtra EExpr → FVarIdSet
| _, .HEq d .. => d.usedLets
| _, _ => default
deriving Inhabited

structure PIData (EExpr : Type) where
P     : PExpr
p     : PExpr
q     : PExpr
extra : PIDataExtra EExpr := .none
usedLets := extra.usedLets
deriving Inhabited



/--
Structured data representing expressions for proofs of equality.
-/
inductive EExpr where
| lam      : LamData EExpr → EExpr
| forallE  : ForallData EExpr → EExpr
| app      : AppData EExpr → EExpr
| trans    : TransData EExpr → EExpr
-- | symm     : SymmData EExpr → EExpr
| refl     : ReflData → EExpr
| fvar     : FVarDataE → EExpr
| lvar     : LVarDataE → EExpr
| prfIrrel : PIData EExpr → EExpr
| sry      : SorryData → EExpr
| unitEta  : UnitEtaData → EExpr
| cast     : CastData EExpr → EExpr
| rev      : EExpr → EExpr -- "thunked" equality reversal
with
  @[computed_field]
  usedLets : @& EExpr → FVarIdSet
  | .lam d
  | .forallE d
  | .app d
  | .trans d
  | .prfIrrel d
  | .rev d
  | .fvar d
  | .lvar d => d.usedLets
  | .refl _ => default
  | .sry _  => default
  | .unitEta _ => default
  | .cast _ => default
-- with
--   @[computed_field]
--   data : @& EExpr → UInt64
-- | .other d
-- | .lam d
-- | .forallE d
-- | .app d
-- | .trans d
-- | .symm d
-- | .refl d
-- | .prfIrrel d
-- | .sry d   => hash d
-- | .rev s t S T l e => hash (#[s, t, S, T], l, data e)
    -- | .const n lvls => mkData (mixHash 5 <| mixHash (hash n) (hash lvls)) 0 0 false false (lvls.any Level.hasMVar) (lvls.any Level.hasParam)
    -- | .bvar idx => mkData (mixHash 7 <| hash idx) (idx+1)
    -- | .sort lvl => mkData (mixHash 11 <| hash lvl) 0 0 false false lvl.hasMVar lvl.hasParam
    -- | .fvar fvarId => mkData (mixHash 13 <| hash fvarId) 0 0 true
    -- | .mvar fvarId => mkData (mixHash 17 <| hash fvarId) 0 0 false true
    -- | .mdata _m e =>
    --   let d := e.data.approxDepth.toUInt32+1
    --   mkData (mixHash d.toUInt64 <| e.data.hash) e.data.looseBVarRange.toNat d e.data.hasFVar e.data.hasExprMVar e.data.hasLevelMVar e.data.hasLevelParam
    -- | .proj s i e =>
    --   let d := e.data.approxDepth.toUInt32+1
    --   mkData (mixHash d.toUInt64 <| mixHash (hash s) <| mixHash (hash i) e.data.hash)
    --       e.data.looseBVarRange.toNat d e.data.hasFVar e.data.hasExprMVar e.data.hasLevelMVar e.data.hasLevelParam
    -- | .app f a => mkAppData f.data a.data
    -- | .lam _ t b _ =>
    --   let d := (max t.data.approxDepth.toUInt32 b.data.approxDepth.toUInt32) + 1
    --   mkDataForBinder (mixHash d.toUInt64 <| mixHash t.data.hash b.data.hash)
    --     (max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1))
    --     d
    --     (t.data.hasFVar || b.data.hasFVar)
    --     (t.data.hasExprMVar || b.data.hasExprMVar)
    --     (t.data.hasLevelMVar || b.data.hasLevelMVar)
    --     (t.data.hasLevelParam || b.data.hasLevelParam)
    -- | .forallE _ t b _ =>
    --   let d := (max t.data.approxDepth.toUInt32 b.data.approxDepth.toUInt32) + 1
    --   mkDataForBinder (mixHash d.toUInt64 <| mixHash t.data.hash b.data.hash)
    --     (max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1))
    --     d
    --     (t.data.hasFVar || b.data.hasFVar)
    --     (t.data.hasExprMVar || b.data.hasExprMVar)
    --     (t.data.hasLevelMVar || b.data.hasLevelMVar)
    --     (t.data.hasLevelParam || b.data.hasLevelParam)
    -- | .letE _ t v b _ =>
    --   let d := (max (max t.data.approxDepth.toUInt32 v.data.approxDepth.toUInt32) b.data.approxDepth.toUInt32) + 1
    --   mkDataForLet (mixHash d.toUInt64 <| mixHash t.data.hash <| mixHash v.data.hash b.data.hash)
    --     (max (max t.data.looseBVarRange.toNat v.data.looseBVarRange.toNat) (b.data.looseBVarRange.toNat - 1))
    --     d
    --     (t.data.hasFVar || v.data.hasFVar || b.data.hasFVar)
    --     (t.data.hasExprMVar || v.data.hasExprMVar || b.data.hasExprMVar)
    --     (t.data.hasLevelMVar || v.data.hasLevelMVar || b.data.hasLevelMVar)
    --     (t.data.hasLevelParam || v.data.hasLevelParam || b.data.hasLevelParam)
    -- | .lit l => mkData (mixHash 3 (hash l))
deriving Inhabited

instance : Coe EExpr (EExpr × FVarIdSet) where
coe e := (e, e.usedLets)

instance : Coe (EExpr × FVarIdSet) EExpr where
coe p := p.1

structure EState where -- TODO why is this needed for dbg_trace to show up?
  -- toExprCache : Std.HashMap EExpr Expr := {}
  -- reverseCache : Std.HashMap EExpr EExpr := {}

abbrev EM := ReaderT EContext <| StateT EState <| Id

def EM.run (dbg : Bool := false) (x : EM α) : α :=
  (StateT.run (x { dbg }) {}).1

def EM.run' (ctx : EContext) (x : EM α) : α :=
  (StateT.run (x ctx) {}).1

def withRev (rev : Bool) (x : EM α) : EM α :=
  withReader (fun ctx => {ctx with rev}) x

def withReversedFVar (d : FVarId) (x : EM α) : EM α :=
  withReader (fun ctx => {ctx with reversedFvars := ctx.reversedFvars.insert d}) x

def withReversedFVars (ds : Array FVarId) (x : EM α) : EM α :=
  withReader (fun ctx => {ctx with reversedFvars := ds.foldl (init := ctx.reversedFvars) fun acc d => acc.insert d}) x

def swapRev (x : EM α) : EM α :=
  withReader (fun ctx => {ctx with rev := not ctx.rev}) x

def rev : EM Bool := do pure (← read).rev 

abbrev ttrace (msg : String) : EM Unit := do
  if (← read).dbg then
    dbg_trace msg


def PExpr.replaceFVar (e fvar val : PExpr) : PExpr := e.toExpr.replaceFVar fvar val |>.toPExpr

def _root_.Lean.LocalDecl.replaceFVar (fvar val : PExpr) (var : LocalDecl) : LocalDecl :=
  assert! not (var.fvarId == fvar.toExpr.fvarId!)
  var.replaceFVarId fvar.toExpr.fvarId! val

-- def _root_.Prod.replaceFVarU (fvar val : PExpr) (Uvar : PExpr × LocalDecl) : PExpr × LocalDecl :=
--   let (U, var) := Uvar
--   (U.replaceFVar fvar val, var.replaceFVar fvar val)
-- mutual
--
-- def HUVData.replaceFVar (fvar val : PExpr) : HUVData EExpr → HUVData EExpr
-- | {a, UaEqVb, extra} => Id.run $ do
--   let extra ← match extra with
--     | .some {b, vaEqb} =>
--       .some {b := b.replaceFVar fvar val, vaEqb := vaEqb.replaceFVar fvar val}
--     | .none => .none
--   {a := a.replaceFVar fvar val, UaEqVb := UaEqVb.replaceFVar fvar val, extra}
--
-- def LamData.replaceFVar (fvar val : PExpr) : LamData EExpr → LamData EExpr
-- | {u, v, A, U, f, a, g, faEqgx, extra} => Id.run $ do
--   let extra ← match extra with
--   | .ABUV {B, hAB, b, vaEqb} {V} =>
--     .ABUV {B := B.replaceFVar fvar val, hAB := hAB.replaceFVar fvar val, b := b.replaceFVar fvar val, vaEqb := vaEqb.replaceFVar fvar val} {V := (V.replaceFVarU fvar val)}
--   | .UV {V} =>
--     .UV {V := V.replaceFVarU fvar val}
--   | .none =>
--     .none
--   {u, v, A := A.replaceFVar fvar val, U := U.replaceFVarU fvar val, f := f.replaceFVar fvar val, a := a.replaceFVar fvar val, g := g.replaceFVar fvar val, faEqgx := faEqgx.replaceFVar fvar val, extra}
--
-- def ForallData.replaceFVar (fvar val : PExpr) : ForallData EExpr → ForallData EExpr
-- | {u, v, A, U, a, extra} => Id.run $ do
--   Id.run $ do
--     let extra := match extra with
--     | .ABUV {B, hAB, b, vaEqb, V, UaEqVx} =>
--       .ABUV {B := B.replaceFVar fvar val, hAB := hAB.replaceFVar fvar val, b := b.replaceFVar fvar val, vaEqb := vaEqb.replaceFVar fvar val, V := V.replaceFVarU fvar val, UaEqVx := UaEqVx.replaceFVar fvar val }
--     | .AB {B, hAB, b, vaEqb} =>
--       .AB {B := B.replaceFVar fvar val, hAB := hAB.replaceFVar fvar val, b := b.replaceFVar fvar val, vaEqb := vaEqb.replaceFVar fvar val }
--     -- | .ABUVApp {b, vaEqb, V, UaEqVx} =>
--     --   .ABUVApp {b := b.replaceFVar fvar val, vaEqb := vaEqb.replaceFVar fvar val, V := V.replaceFVarU fvar val, UaEqVx := UaEqVx.replaceFVar fvar val}
--     | .UV {V, UaEqVx} =>
--       .UV {V := V.replaceFVarU fvar val, UaEqVx := UaEqVx.replaceFVar fvar val }
--     {u, v, A := A.replaceFVar fvar val, U := U.replaceFVarU fvar val, a := a.replaceFVar fvar val, extra}
--
-- def AppData.replaceFVar (fvar val : PExpr) : AppData EExpr → AppData EExpr
-- | {u, v, A, U, f, a, extra} => Id.run $ do
--   let extra := match extra with
--   | .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb} =>
--     .ABUV {B := B.replaceFVar fvar val, hAB := hAB.replaceFVar fvar val, V := V.replaceFVarU fvar val, hUV := hUV.replaceFVar fvar val, g := g.replaceFVar fvar val, fEqg := fEqg.replaceFVar fvar val, b := b.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val}
--   | .UV {V, hUV, g, fEqg, b, aEqb} =>
--     .UV {V := V.replaceFVarU fvar val, hUV := hUV.replaceFVar fvar val, g := g.replaceFVar fvar val, fEqg := fEqg.replaceFVar fvar val, b := b.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val}
--   | .UVFun {V, hUV, g, fEqg} =>
--     .UVFun {V := V.replaceFVarU fvar val, hUV := hUV.replaceFVar fvar val, g := g.replaceFVar fvar val, fEqg := fEqg.replaceFVar fvar val}
--   | .AB {B, hAB, g, fEqg, b, aEqb} =>
--     .AB {B := B.replaceFVar fvar val, hAB := hAB.replaceFVar fvar val, g := g.replaceFVar fvar val, fEqg := fEqg.replaceFVar fvar val, b := b.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val}
--   | .none {g, fEqg, b, aEqb} =>
--     .none {g := g.replaceFVar fvar val, fEqg := fEqg.replaceFVar fvar val, b := b.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val}
--   | .Fun {g, fEqg} =>
--     .Fun {g := g.replaceFVar fvar val, fEqg := fEqg.replaceFVar fvar val}
--   | .Arg {b, aEqb} =>
--     .Arg {b := b.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val}
--   {u, v, A := A.replaceFVar fvar val, U := U.replaceFVarU fvar val, f := f.replaceFVar fvar val, a := a.replaceFVar fvar val, extra}
--
-- def TransData.replaceFVar (fvar val : PExpr) : TransData EExpr → TransData EExpr
-- | {u, A, B, C, a, b, c, aEqb, bEqc} =>
--   {u, A := A.replaceFVar fvar val, B := B.replaceFVar fvar val, C := C.replaceFVar fvar val, a := a.replaceFVar fvar val, b := b.replaceFVar fvar val, c := c.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val, bEqc := bEqc.replaceFVar fvar val}
--
-- -- def SymmData.replaceFVar (fvar val : PExpr) : SymmData EExpr → SymmData EExpr
-- -- | {u, A, B, a, b, aEqb} =>
-- --   {u, A := A.replaceFVar fvar val, B := B.replaceFVar fvar val, a := a.replaceFVar fvar val, b := b.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val}
--
-- def ReflData.replaceFVar (fvar val : PExpr) : ReflData → ReflData
-- | {u, A, a, n} =>
--   {u, A := A.replaceFVar fvar val, a := a.replaceFVar fvar val, n}
--
-- def PIData.replaceFVar (fvar val : PExpr) : PIData EExpr → PIData EExpr
-- | {P, p, q, extra} => Id.run $ do
--   let extra := match extra with
--   | .none =>
--     .none
--   | .HEq {Q, hPQ} =>
--     .HEq {Q := Q.replaceFVar fvar val, hPQ := hPQ.replaceFVar fvar val}
--   {P := P.replaceFVar fvar val, p := p.replaceFVar fvar val, q := q.replaceFVar fvar val, extra}
--
-- def FVarData.replaceFVar (fvar val : PExpr) : FVarData → FVarData
-- | {aEqb, bEqa} => {aEqb := aEqb.replaceFVar fvar val, bEqa := bEqa.replaceFVar fvar val}
--
-- def FVarDataE.replaceFVar (fvar val : PExpr) : FVarDataE → FVarDataE
-- | {u, A, a, B, b, aEqb, bEqa} => {u, A := A.replaceFVar fvar val, a := a.replaceFVar fvar val, B := B.replaceFVar fvar val, b := b.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val, bEqa := bEqa.replaceFVar fvar val}
--
-- def SorryData.replaceFVar (fvar val : PExpr) : SorryData → SorryData
-- | {u, A, a, B, b} => {u, A := A.replaceFVar fvar val, a := a.replaceFVar fvar val, B := B.replaceFVar fvar val, b := b.replaceFVar fvar val}
--
-- def EExpr.replaceFVar (fvar val : PExpr) : EExpr → EExpr
-- | .lam d      => .lam      $ d.replaceFVar fvar val
-- | .forallE d  => .forallE  $ d.replaceFVar fvar val
-- | .app d      => .app      $ d.replaceFVar fvar val
-- | .trans d    => .trans    $ d.replaceFVar fvar val
-- | .fvar d     => .fvar     $ d.replaceFVar fvar val
-- -- | .symm d     => .symm     $ d.replaceFVar fvar val
-- | .refl d     => .refl     $ d.replaceFVar fvar val
-- | .prfIrrel d => .prfIrrel $ d.replaceFVar fvar val
-- | .sry d      => .sry      $ d.replaceFVar fvar val
-- | .rev e      => .rev (e.replaceFVar fvar val)
--
-- end
--
-- def EExpr.replaceFVars (fvars vals : Array PExpr) (e : EExpr) : EExpr := Id.run $ do
--   let mut ret := e
--   for (var, val) in fvars.zip vals do
--     ret := ret.replaceFVar var val
--   pure ret

-- structure EExpr' where -- TODO why is this needed???
-- expr : EExpr
-- deriving Inhabited
--
-- instance : Coe EExpr' EExpr where
-- coe e := e.expr
--
-- -- instance : SizeOf EExpr where
-- -- sizeOf e := sorry
-- --
-- def _root_.Lean.Expr.replaceFVarE (e fvar : Expr) : PExpr :=
--   assert! not (e.containsFVar' fvar.fvarId!)
--   e.toPExpr
--
-- def PExpr.replaceFVarE (e fvar : PExpr) : PExpr := e.toExpr.replaceFVarE fvar
--
-- def _root_.Lean.LocalDecl.replaceFVarE (fvar : PExpr) (var : LocalDecl) : LocalDecl :=
--   assert! not (var.fvarId == fvar.toExpr.fvarId!)
--   assert! not (var.type.containsFVar' fvar.toExpr.fvarId!)
--   var
--
-- def _root_.Prod.replaceFVarEU (fvar : PExpr) (Uvar : PExpr × LocalDecl) : PExpr × LocalDecl :=
--   let (U, var) := Uvar
--   (U.replaceFVarE fvar, var.replaceFVarE fvar)
-- mutual
--
-- def HUVData.replaceFVarE (fvar : PExpr) (val : EExpr') : HUVData EExpr → EM (HUVData EExpr)
-- | {a, UaEqVb, extra} => do
--   let extra ← match extra with
--     | .some {b, vaEqb} =>
--       pure $ .some {b := b.replaceFVarE fvar, vaEqb := vaEqb.replaceFVarE fvar}
--     | .none => pure .none
--   pure {a := a.replaceFVarE fvar, UaEqVb := (← UaEqVb.replaceFVarE fvar val), extra}
--
-- def LamData.replaceFVarE (fvar : PExpr) (val : EExpr') : LamData EExpr → EM (LamData EExpr)
-- | {u, v, A, U, f, a, g, faEqgx, extra} => do
--   let extra ← match extra with
--   | .ABUV {B, hAB, b, vaEqb} {V} =>
--     pure $ .ABUV {B := B.replaceFVarE fvar, hAB := (← hAB.replaceFVarE fvar val), b := b.replaceFVarE fvar, vaEqb := vaEqb.replaceFVarE fvar} {V := (V.replaceFVarEU fvar)}
--   | .UV {V} =>
--     pure $ .UV {V := V.replaceFVarEU fvar}
--   | .none =>
--     pure .none
--   pure {u, v, A := A.replaceFVarE fvar, U := U.replaceFVarEU fvar, f := f.replaceFVarE fvar, a := a.replaceFVarE fvar, g := g.replaceFVarE fvar, faEqgx := (← faEqgx.replaceFVarE fvar val), extra}
--
-- def ForallData.replaceFVarE (fvar : PExpr) (val : EExpr') : ForallData EExpr → EM (ForallData EExpr)
-- | {u, v, A, U, a, extra} => do
--   let extra ← match extra with
--   | .ABUV {B, hAB, b, vaEqb, V, UaEqVx } =>
--     pure $ .ABUV {B := B.replaceFVarE fvar, hAB := (← hAB.replaceFVarE fvar val), b := b.replaceFVarE fvar, vaEqb := vaEqb.replaceFVarE fvar, V := V.replaceFVarEU fvar, UaEqVx := (← UaEqVx.replaceFVarE fvar val)}
--   | .AB {B, hAB, b, vaEqb } =>
--     pure $ .AB {B := B.replaceFVarE fvar, hAB := (← hAB.replaceFVarE fvar val), b := b.replaceFVarE fvar, vaEqb := vaEqb.replaceFVarE fvar }
--   | .UV {V, UaEqVx}  =>
--     pure $ .UV {V := V.replaceFVarEU fvar, UaEqVx := (← UaEqVx.replaceFVarE fvar val)}
--   pure {u, v, A := A.replaceFVarE fvar, U := U.replaceFVarEU fvar, a := a.replaceFVarE fvar, extra}
--
-- def AppData.replaceFVarE (fvar : PExpr) (val : EExpr') : AppData EExpr → EM (AppData EExpr)
-- | {u, v, A, U, f, a, extra} => do
--   let extra ← match extra with
--   | .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb} =>
--     pure $ .ABUV {B := B.replaceFVarE fvar, hAB := (← hAB.replaceFVarE fvar val), V := V.replaceFVarEU fvar, hUV := (← hUV.replaceFVarE fvar val), g := g.replaceFVarE fvar, fEqg := (← fEqg.replaceFVarE fvar val), b := b.replaceFVarE fvar, aEqb := (← aEqb.replaceFVarE fvar val)}
--   | .UV {V, hUV, g, fEqg, b, aEqb} =>
--     pure $ .UV {V := V.replaceFVarEU fvar, hUV := (← hUV.replaceFVarE fvar val), g := g.replaceFVarE fvar, fEqg := (← fEqg.replaceFVarE fvar val), b := b.replaceFVarE fvar, aEqb := (← aEqb.replaceFVarE fvar val)}
--   | .UVFun {V, hUV, g, fEqg} =>
--     pure $ .UVFun {V := V.replaceFVarEU fvar, hUV := (← hUV.replaceFVarE fvar val), g := g.replaceFVarE fvar, fEqg := (← fEqg.replaceFVarE fvar val)}
--   | .AB {B, hAB, g, fEqg, b, aEqb} =>
--     pure $ .AB {B := B.replaceFVarE fvar, hAB := (← hAB.replaceFVarE fvar val), g := g.replaceFVarE fvar, fEqg := (← fEqg.replaceFVarE fvar val), b := b.replaceFVarE fvar, aEqb := (← aEqb.replaceFVarE fvar val)}
--   | .none {g, fEqg, b, aEqb} =>
--     pure $ .none {g := g.replaceFVarE fvar, fEqg := (← fEqg.replaceFVarE fvar val), b := b.replaceFVarE fvar, aEqb := (← aEqb.replaceFVarE fvar val)}
--   | .Fun {g, fEqg} =>
--     pure $ .Fun {g := g.replaceFVarE fvar, fEqg := (← fEqg.replaceFVarE fvar val)}
--   | .Arg {b, aEqb} =>
--     pure $ .Arg {b := b.replaceFVarE fvar, aEqb := (← aEqb.replaceFVarE fvar val)}
--   pure {u, v, A := A.replaceFVarE fvar, U := U.replaceFVarEU fvar, f := f.replaceFVarE fvar, a := a.replaceFVarE fvar, extra}
--
-- def TransData.replaceFVarE (fvar : PExpr) (val : EExpr') : TransData EExpr → EM (TransData EExpr)
-- | {u, A, B, C, a, b, c, aEqb, bEqc} => do
--   pure {u, A := A.replaceFVarE fvar, B := B.replaceFVarE fvar, C := C.replaceFVarE fvar, a := a.replaceFVarE fvar, b := b.replaceFVarE fvar, c := c.replaceFVarE fvar, aEqb := (← aEqb.replaceFVarE fvar val), bEqc := (← bEqc.replaceFVarE fvar val)}
--
-- -- def SymmData.replaceFVarE (fvar : PExpr) (val : EExpr') : SymmData EExpr → EM (SymmData EExpr)
-- -- | {u, A, B, a, b, aEqb} => do
-- --   pure {u, A := A.replaceFVarE fvar, B := B.replaceFVarE fvar, a := a.replaceFVarE fvar, b := b.replaceFVarE fvar, aEqb := (← aEqb.replaceFVarE fvar val)}
--
-- def ReflData.replaceFVarE (fvar : PExpr) : ReflData → ReflData
-- | {u, A, a, n} =>
--   {u, A := A.replaceFVarE fvar, a := a.replaceFVarE fvar, n}
--
-- def PIData.replaceFVarE (fvar : PExpr) (val : EExpr') : PIData EExpr → EM (PIData EExpr)
-- | {P, p, q, extra} => do
--   let extra ← match extra with
--   | .none =>
--     pure .none
--   | .HEq {Q, hPQ} =>
--     pure $ .HEq {Q := Q.replaceFVarE fvar, hPQ := (← hPQ.replaceFVarE fvar val)}
--   pure {P := P.replaceFVarE fvar, p := p.replaceFVarE fvar, q := q.replaceFVarE fvar, extra}
--
-- def FVarData.replaceFVarE (fvar : PExpr) : FVarData → FVarData
-- | {aEqb, bEqa} => {aEqb := aEqb.replaceFVarE fvar, bEqa := bEqa.replaceFVarE fvar}
--
-- -- def FVarDataE.replaceFVarE (fvar val : PExpr) : FVarDataE → FVarData
-- -- | d@{aEqb, ..} => {aEqb := aEqb.replaceFVarE fvar, bEqa := bEqa.replaceFVarE fvar}
--
-- def SorryData.replaceFVarE (fvar : PExpr) : SorryData → SorryData
-- | {u, A, a, B, b} => {u, A := A.replaceFVarE fvar, a := a.replaceFVarE fvar, B := B.replaceFVarE fvar, b := b.replaceFVarE fvar}
--
-- def EExpr.replaceFVarE (fvar : PExpr) (val : EExpr') (e : EExpr) : EM EExpr := do
-- match e with
-- | .lam d      => pure $ .lam      $ (← d.replaceFVarE fvar val)
-- | .forallE d  => pure $ .forallE  $ (← d.replaceFVarE fvar val)
-- | .app d      => pure $ .app      $ (← d.replaceFVarE fvar val)
-- | .trans d    => pure $ .trans    $ (← d.replaceFVarE fvar val)
-- | .fvar {aEqb, ..} => if aEqb.fvarId == fvar.toExpr.fvarId! then pure val else pure e
-- -- | .symm d     =>
-- --   let d' ← d.replaceFVarE fvar val
-- --   match d'.aEqb with
-- --   | .symm de => pure $ de.aEqb -- can eliminate double-symm application
-- --   | _ => pure $ .symm d'
-- | .refl d     => pure $ .refl     $ d.replaceFVarE fvar
-- | .prfIrrel d => pure $ .prfIrrel $ (← d.replaceFVarE fvar val)
-- | .sry d      => pure $ .sry      $ d.replaceFVarE fvar
-- | .rev e => pure $ .rev (← e.replaceFVarE fvar val)
--
-- end

-- -- def EExpr.reverse : EExpr → EExpr
-- -- | other   (e : Expr) => sorry
-- -- | lam     (d : LamData EExpr) => sorry
-- -- | forallE (d : ForallData EExpr) => sorry
-- -- | app     (d : AppData EExpr) => sorry
-- mutual
--
-- def FVarData.reverse : FVarData → FVarData
-- | {aEqb, bEqa} => Id.run $ do
--   pure {aEqb := bEqa, bEqa := aEqb} 
--
-- def LamData.reverse : LamData EExpr → EM EExpr
-- | {u, v, A, U, f, a, g, faEqgx, extra} => do
--     let (extra, newA, newU, newa, newfaEqgx) ← match extra with
--     | .ABUV {b, B, vaEqb, hAB} {V} => do
--       let aEqb' := .mk $ EExpr.symm {u, a := b.toExpr.toPExpr, b := a.toExpr.toPExpr, A := B, B := A, aEqb := EExpr.other (vaEqb.bEqa.toExpr.toPExpr)}
--       let newfaEqgx ← (← EExpr.reverse 1 f g (mkForall #[U.2] U.1) (mkForall #[U.2] U.1) (Level.imax u v) faEqgx) |>.replaceFVarE (vaEqb.aEqb.toExpr.toPExpr) aEqb'
--       pure (.ABUV {b := a, B := A, vaEqb := vaEqb.reverse, hAB := (← (← EExpr.reverse 2 A B (Expr.sort u).toPExpr (Expr.sort u).toPExpr u.succ hAB).replaceFVarE (vaEqb.aEqb.toExpr.toPExpr) aEqb')} {V := U}, B, V, b, newfaEqgx)
--     | .UV {V} => pure (.UV {V := U}, A, V, a, (← EExpr.reverse 3 f g (mkForall #[U.2] U.1) (mkForall #[U.2] U.1) (Level.imax u v) faEqgx))
--     | .none => pure (.none, A, U, a, (← EExpr.reverse 4 f g (mkForall #[U.2] U.1) (mkForall #[U.2] U.1) (Level.imax u v) faEqgx))
--     pure $ .lam {u, v, A := newA, U := newU, f := g, a := newa, g := f, faEqgx := newfaEqgx, extra}
--
-- def HUVData.reverse (A B Ua Vb : PExpr) (u v : Level) : HUVData EExpr → EM (HUVData EExpr)
-- | {a, UaEqVb, extra} => do
--   let newUaEqVb ← UaEqVb.reverse 5 Ua Vb (Expr.sort v).toPExpr (Expr.sort v).toPExpr v.succ
--   let ret ← match extra with
--   | .some {b, vaEqb} => do
--     let aEqb' := .mk $ EExpr.symm {u, a := b.toExpr.toPExpr, b := a.toExpr.toPExpr, A := B, B := A, aEqb := EExpr.other (vaEqb.bEqa.toExpr.toPExpr)}
--     pure {a := b, UaEqVb := (← newUaEqVb.replaceFVarE (vaEqb.aEqb.toExpr.toPExpr) aEqb'), extra := .some {b := a, vaEqb := vaEqb.reverse}}
--   | .none => pure {a, UaEqVb := newUaEqVb, extra := .none}
--   pure ret
--
-- def ForallData.reverse : ForallData EExpr → EM EExpr
--   | {u, v, A, U, V, a, UaEqVx, extra} => do 
--     let (extra, newA, newa) ← match extra with
--     | .AB {b, B, hAB, vaEqb} => do
--       let aEqb' := .mk $ EExpr.symm {u, a := b.toExpr.toPExpr, b := a.toExpr.toPExpr, A := B, B := A, aEqb := EExpr.other (vaEqb.bEqa.toExpr.toPExpr)}
--       pure (.AB {b := a, B := A, hAB := (← (← hAB.reverse 6 A B (Expr.sort u).toPExpr (Expr.sort u).toPExpr u.succ).replaceFVarE (vaEqb.aEqb.toExpr.toPExpr) aEqb'), vaEqb := vaEqb.reverse}, B, b)
--     | .ABApp {b, vaEqb} => 
--       pure (.ABApp {b := a, vaEqb := vaEqb.reverse}, A, b)
--     | .none =>
--       pure (.none, A, a)
--
--     let newUaEqVx ← UaEqVx.reverse 7 U.1 V.1 (Expr.sort v).toPExpr (Expr.sort v).toPExpr v.succ
--     pure $ .forallE {u, v, A := newA, U := V, V := U, a := newa, UaEqVx := newUaEqVx, extra}
--
-- def AppData.reverse (n : Nat) : AppData EExpr → EM EExpr
-- | {u, v, A, U, f, a, extra} => do
--   let (extra, newA, newU, newf, newa) ← match extra with
--   | .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb} =>
--     pure (.ABUV {B := A, hAB := (← EExpr.reverse 8 A B (Expr.sort u).toPExpr (Expr.sort u).toPExpr u.succ hAB), V := U, hUV := (← HUVData.reverse A B (Prod.fst U) (Prod.fst V) u v hUV), g := f, fEqg := (← EExpr.reverse 9 f g (mkForall #[U.2] U.1) (mkForall #[V.2] V.1) (Level.imax u v) fEqg), b := a, aEqb := (← EExpr.reverse 10 a b A B u aEqb)}, B, V, g, b)
--   | .UV {V, hUV, g, fEqg, b, aEqb} => 
--     pure $ (.UV {V := U, hUV := (← HUVData.reverse A A (Prod.fst U) (Prod.fst V) u v hUV), g := f, fEqg := (← EExpr.reverse 11 f g (mkForall #[U.2] U.1) (mkForall #[V.2] V.1) (Level.imax u v) fEqg), b := a, aEqb := (← EExpr.reverse 12 a b A A u aEqb)}, A, V, g, b)
--   | .UVFun {V, hUV, g, fEqg} => 
--     pure (.UVFun {V := U, hUV := (← HUVData.reverse A A (Prod.fst U) (Prod.fst V) u v hUV), g := f, fEqg := (← EExpr.reverse 13 f g (mkForall #[U.2] U.1) (mkForall #[V.2] V.1) (Level.imax u v) fEqg)}, A, V, g, a)
--   | .AB {B, hAB, g, fEqg, b, aEqb} => 
--     pure (.AB {B := A, hAB := (← EExpr.reverse 14 A B (Expr.sort u).toPExpr (Expr.sort u).toPExpr u.succ hAB), g := f, fEqg := (← EExpr.reverse 15 f g (mkForall #[U.2] U.1) (mkForall #[U.2] U.1) (Level.imax u v) fEqg), b := a, aEqb := (← EExpr.reverse 16 a b A B u aEqb)}, B, U, g, b)
--   | .none {g, fEqg, b, aEqb} =>
--     pure (.none {g := f, fEqg := (← EExpr.reverse 17 f g (mkForall #[U.2] U.1) (mkForall #[U.2] U.1) (Level.imax u v) fEqg), b := a, aEqb := (← EExpr.reverse 18 a b A A u aEqb)}, A, U, g, b)
--   | .Fun {g, fEqg} =>
--     pure (.Fun {g := f, fEqg := (← EExpr.reverse 19 f g (mkForall #[U.2] U.1) (mkForall #[U.2] U.1) (Level.imax u v) fEqg)}, A, U, g, a)
--   | .Arg {b, aEqb} =>
--     pure (.Arg {b := a, aEqb := (← EExpr.reverse 20 a b A A u aEqb)}, A, U, f, b)
--   pure $ .app {u, v, A := newA, U := newU, f := newf, a := newa, extra}
--
-- def TransData.reverse : TransData EExpr → EM EExpr
-- | {u, A, B, C, a, b, c, aEqb, bEqc} => do
--   pure $ .trans {u, A := C, B, C := A, a := c, b, c := a, aEqb := (← bEqc.reverse 21 b c B C u), bEqc := (← aEqb.reverse 22 a b A B u)}
--
-- def SymmData.reverse : SymmData EExpr → EM EExpr
-- | {aEqb, ..} => pure aEqb
--
-- def ReflData.reverse : ReflData → EM EExpr := fun d => pure $ .refl d
--
-- def PIData.reverse : PIData EExpr → EM EExpr
-- | {P, p, q, extra} => do
--   let (extra, newP) ← match extra with
--   | .none => pure (.none, P)
--   | .HEq {Q, hPQ} =>
--     pure (.HEq {Q := P, hPQ := (← hPQ.reverse 23 P Q (Expr.sort 0).toPExpr (Expr.sort 0).toPExpr 1)}, Q)
--   pure $ .prfIrrel {P := newP, p := q, q := p, extra := extra}
--
-- def SorryData.reverse : SorryData → EM EExpr
-- | {u, a, A, b, B} =>
--   pure $ .sry {u, A := B, a := b, B := A, b := a}
--
-- def EExpr.reverse (n : Nat) (t s tType sType : PExpr) (lvl : Level) (e : EExpr) : EM EExpr := do
--   -- if let some ex := (← get).reverseCache[e]? then
--   --   return ex
--   let ret ← match e with
--     | .other e => pure $ .symm {u := lvl, A := tType, B := sType, a := t, b := s, aEqb := .other e}
--     | .app d  => d.reverse n
--     | .lam d
--     | .forallE d
--     | .trans d
--     | .symm d
--     | .refl d
--     | .prfIrrel d
--     | .sry d  => d.reverse
--     | .rev _ _ _ _ _ e => pure e
--   -- modify fun st => { st with reverseCache := st.reverseCache.insert e ret }
--   pure ret
--
-- -- def EExpr.reverse? : EExpr → Option EExpr
-- -- | .other _ => none
-- -- | .lam d
-- -- | .forallE d
-- -- | .app d
-- -- | .trans d
-- -- | .symm d
-- -- | .refl d
-- -- | .prfIrrel d
-- -- | .sry d  => d.reverse
-- -- | .rev _ _ _ _ _ e => e
--
-- end

def expandLets' (lets : Array LocalDeclE) (e : Expr) : EM Expr := do
  let mut newLets := #[]
  let mut prevLetVars := #[]
  for l in lets do
    newLets := newLets.push $ (l.value (← read)).replaceFVars prevLetVars newLets
    prevLetVars := prevLetVars.push (.fvar l.fvarId)
  let ret := e.replaceFVars prevLetVars newLets
  pure ret

def expandLets (lets : Array LocalDecl) (e : Expr) : Expr := Id.run $ do
  let ret := (expandLets' (lets.map fun l => .mk l.index l.fvarId l.userName l.type default (fun _ => l.value)) e).run
  pure ret

def expandLetsForall (lctx : LocalContext) (fvars : Array Expr) (lets : Array (Array LocalDecl)) (e : Expr) : Expr := Id.run $ do
  let mut ret := e
  for (fv, ls) in fvars.zip lets |>.reverse do
    ret := lctx.mkForall #[fv] (expandLets ls ret) |>.toPExpr
  pure ret

def expandLetsLambda (lctx : LocalContext) (fvars : Array Expr) (lets : Array (Array LocalDecl)) (e : Expr) : Expr := Id.run $ do
  let mut ret := e
  for (fv, ls) in fvars.zip lets |>.reverse do
    ret := lctx.mkLambda #[fv] (expandLets ls ret) |>.toPExpr
  pure ret
  -- (expandLets' lets e).run {}

def mkLambda (vars : Array LocalDecl) (b : Expr) : EM PExpr := do
  pure $ LocalContext.mkLambda (vars.foldl (init := default) fun lctx decl => lctx.addDecl decl) (vars.map (·.toExpr)) b |>.toPExpr

def mkForall (vars : Array LocalDecl) (b : Expr) : PExpr := LocalContext.mkForall (vars.foldl (init := default) fun lctx decl => lctx.addDecl decl) (vars.map (·.toExpr)) b |>.toPExpr

def getMaybeDepLemmaApp (Uas : Array PExpr) (as : Array LocalDecl) : EM $ Array PExpr × Bool := do
  let dep := Uas.zip as |>.foldl (init := false) fun acc (Ua, a) =>
    Ua.toExpr.containsFVar' a.fvarId || acc
  let ret ← Uas.zip as |>.mapM fun (Ua, a) => do
    if dep then
      mkLambda #[a] Ua
    else
      pure Ua
  pure (ret, dep)

def getMaybeDepLemmaApp1 (U : PExpr × LocalDecl) : EM (PExpr × Bool) := do
  let (Ua, a) := U
  match ← getMaybeDepLemmaApp #[Ua] #[a] with
  | (#[U], dep) => pure (U, dep)
  | _ => unreachable!

def getMaybeDepLemmaApp2 (U V : (PExpr × LocalDecl)) : EM (PExpr × PExpr × Bool) := do
  let (Ua, a) := U
  let (Vb, b) := V
  match ← getMaybeDepLemmaApp #[Ua, Vb] #[a, b] with
  | (#[U, V], dep) => pure (U, V, dep)
  | _ => unreachable!

mutual
def HUVData.toExprDep' (e : HUVData EExpr) : EM Expr := match e with -- FIXME why can't I use a single function here?
| {a, UaEqVb, extra, alets, ..} => do
  let ret ← if (← rev) then withReversedFVars (alets.map (·.fvarId)) do
    match extra with
      | .some {b, vaEqb, blets, ..} => withReversedFVars (#[vaEqb.aEqb.fvarId] ++ blets.map (·.fvarId) ++ vaEqb.lets.map (·.fvarId)) do
        let h ← expandLets' (alets ++ blets ++ vaEqb.lets) (← UaEqVb.1.toExpr')
        -- mkLambda (← expandLets #[(b, blets), (a, alets), (vaEqb.bEqa, vaEqb.lets)]) (← UaEqVb.1.toExpr') -- TODO fix let variable ordering (should be same as context order)
        mkLambda #[b, a, vaEqb.bEqa] h
      | .none =>
        let h ← expandLets' alets (← UaEqVb.1.toExpr')
        mkLambda #[a] h
  else
    match extra with
      | .some {b, vaEqb, blets, ..} =>
        let h ← expandLets' (alets ++ blets ++ vaEqb.lets) (← UaEqVb.1.toExpr')
        mkLambda #[a, b, vaEqb.aEqb] h
      | .none => 
        let h ← expandLets' alets (← UaEqVb.1.toExpr')
        mkLambda #[a] h
  pure ret

def HUVData.toExpr' (e : HUVData EExpr) : EM Expr := match e with
| {UaEqVb, ..} => do
  pure (← UaEqVb.1.toExpr')

def LamDataExtra.lemmaName (dep : Bool) (d : LamDataExtra EExpr) : Name :=
let name := match d with
| .ABUV .. => `L4L.lambdaHEqABUV
| .UV .. => `L4L.lambdaHEqUV
| .none => `L4L.lambdaHEq
if dep then name.toString ++ "'" |>.toName else name

def dbgFIds := #["_kernel_fresh.3032".toName, "_kernel_fresh.3036".toName, "_kernel_fresh.910".toName, "_kernel_fresh.914".toName]

def LamData.toExpr (e : LamData EExpr) : EM Expr := match e with
| {u, v, A, U, f, a, g, faEqgx, extra, alets, ..} => do
  if (← rev) then withReversedFVars (alets.map (·.fvarId)) do
    let hfg ← match extra with
    | .ABUV {b, vaEqb, blets, ..} .. => withReversedFVars (#[vaEqb.aEqb.fvarId] ++ blets.map (·.fvarId) ++ vaEqb.lets.map (·.fvarId)) do
      let h ← expandLets' (alets ++ blets ++ vaEqb.lets) (← faEqgx.1.toExpr')
      mkLambda #[b, a, vaEqb.bEqa] h
    | .UV ..
    | .none =>
      let h ← expandLets' alets (← faEqgx.1.toExpr')
      mkLambda #[a] h

    let (args, dep) ← match extra with
    | .ABUV {B, hAB, ..} {V} =>
        let (U, V, dep) ← getMaybeDepLemmaApp2 U V
        pure $ (#[B.toExpr, A, V, U, g, f, (← hAB.1.toExpr'), hfg], dep)
    | .UV {V} => 
        let (U, V, dep) ← getMaybeDepLemmaApp2 U V
        pure (#[A.toExpr, V, U, g, f, hfg], dep)
    | .none => 
        let (U, dep) ← getMaybeDepLemmaApp1 U
        pure (#[A.toExpr, U, g, f, hfg], dep)
    let n := extra.lemmaName dep
    pure $ Lean.mkAppN (.const n [u, v]) args
  else
    let hfg ← match extra with
    | .ABUV {b, vaEqb, blets, ..} .. =>
      let h ← expandLets' (alets ++ blets ++ vaEqb.lets) (← faEqgx.1.toExpr')
      mkLambda #[a, b, vaEqb.aEqb] h
    | .UV ..
    | .none =>
      let h ← expandLets' alets (← faEqgx.1.toExpr')
      mkLambda #[a] h

    let (args, dep, U) ← match extra with
    | .ABUV {B, hAB, b, ..} {V} =>
        let (U, V, dep) ← getMaybeDepLemmaApp2 U V
        -- if dbgFIds.any (· == a.fvarId.name) then
        --   dbg_trace s!"DBG[0]: {a.fvarId.name}, {b.fvarId.name}, {dep}, {Lean.collectFVars default V |>.fvarIds.map (·.name)}"
        pure $ (#[A.toExpr, B, U, V, f, g, (← hAB.1.toExpr'), hfg], dep, V)
    | .UV {V} => 
        let (U, V, dep) ← getMaybeDepLemmaApp2 U V
        pure (#[A.toExpr, U, V, f, g, hfg], dep, U)
    | .none => 
        let (U, dep) ← getMaybeDepLemmaApp1 U
        pure (#[A.toExpr, U, f, g, hfg], dep, U)

    let n := extra.lemmaName dep
    pure $ Lean.mkAppN (.const n [u, v]) args

def ForallDataExtra.lemmaName (dep : Bool) (d : ForallDataExtra EExpr) : Name :=
let name := match d with
| .ABUV .. => `L4L.forallHEqABUV
| .AB .. => `L4L.forallHEqAB
| .UV .. => `L4L.forallHEqUV
if dep then name.toString ++ "'" |>.toName else name

def ForallData.toExpr (e : ForallData EExpr) : EM Expr := match e with
| {u, v, A, U, a, extra, alets, ..} => do

  let (U, V?, dep) ← do
    match extra with
    | .ABUV {V, ..}
    | .UV {V, ..} =>
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (U, V, dep)
    | .AB {..} => 
      let (U, dep) ← getMaybeDepLemmaApp1 U
      assert! not dep
      pure (U, default, dep)

  let (args, dep) ← if (← rev) then
    let hUV dep := do withReversedFVars (alets.map (·.fvarId)) do
      if dep then
        match extra with
        | .ABUV {b, vaEqb, UaEqVx, blets, ..} => withReversedFVars (#[vaEqb.aEqb.fvarId] ++ blets.map (·.fvarId) ++ vaEqb.lets.map (·.fvarId)) do
          let h ← expandLets' (alets ++ blets ++ vaEqb.lets) (← UaEqVx.1.toExpr')
          -- mkLambda (← expandLets #[(b, blets), (a, alets), (vaEqb.bEqa, vaEqb.lets)]) (← UaEqVb.1.toExpr') -- TODO fix let variable ordering (should be same as context order)
          mkLambda #[b, a, vaEqb.bEqa] h
        | .UV {UaEqVx, ..} =>
          let h ← expandLets' alets (← UaEqVx.1.toExpr')
          mkLambda #[a] h
        | _ => unreachable!
      else
        match extra with
        | .ABUV {UaEqVx, ..} =>
          pure $ ← expandLets' alets (← UaEqVx.1.toExpr').toPExpr
        | .UV {UaEqVx, ..} =>
          pure $ ← expandLets' alets (← UaEqVx.1.toExpr').toPExpr
        | _ => unreachable!

    match extra with
    | .ABUV {B, hAB, ..} =>
      pure $ (#[B.toExpr, A, V?, U, (← hAB.1.toExpr'), (← hUV dep)], dep)
    | .UV .. =>
      pure (#[A.toExpr, V?, U, (← hUV dep)], dep)
    | .AB {B, hAB, ..} =>
      pure (#[B.toExpr, A.toExpr, U, (← hAB.1.toExpr')], dep)
  else
    let hUV dep := do
      if dep then
        match extra with
        | .ABUV {b, vaEqb, UaEqVx, blets, ..} =>
          let h ← expandLets' (alets ++ blets ++ vaEqb.lets) (← UaEqVx.1.toExpr')
          mkLambda #[a, b, vaEqb.aEqb] h
        | .UV {UaEqVx, ..} =>
          let h ← expandLets' alets (← UaEqVx.1.toExpr')
          mkLambda #[a] h
        | _ => unreachable!
      else
        match extra with
        | .ABUV {UaEqVx, ..} =>
          pure $ ← expandLets' alets (← UaEqVx.1.toExpr').toPExpr
        | .UV {UaEqVx, ..} =>
          pure $ ← expandLets' alets (← UaEqVx.1.toExpr').toPExpr
        | _ => unreachable!

    match extra with
    | .ABUV {B, hAB, ..} =>
      pure $ (#[A.toExpr, B, U, V?, (← hAB.1.toExpr'), (← hUV dep)], dep)
    | .UV .. =>
      pure (#[A.toExpr, U, V?, (← hUV dep)], dep)
    | .AB {B, hAB, ..} =>
      pure (#[A.toExpr, B.toExpr, U, (← hAB.1.toExpr')], dep)

  let n := extra.lemmaName dep
  pure $ Lean.mkAppN (.const n [u, v]) args

def AppDataExtra.lemmaName (dep : Bool) (d : AppDataExtra EExpr) : Name :=
let name := match d with
| .ABUV .. => `L4L.appHEqABUV
| .UV .. => `L4L.appHEqUV
| .UVFun .. => `L4L.appFunHEqUV
| .AB .. => `L4L.appHEqAB
| .none .. => `L4L.appHEq
| .Arg .. => `L4L.appArgHEq
| .Fun .. => `L4L.appFunHEq
if dep then name.toString ++ "'" |>.toName else name

def AppData.toExpr (e : AppData EExpr) : EM Expr := match e with
| {u, v, A, U, f, a, extra, ..} => do
  let (args, dep) ← if (← rev) then
    match extra with
    | .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb, ..} =>
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (#[B.toExpr, A, V, U, (← hAB.1.toExpr'), (← if dep then do hUV.toExprDep' else hUV.toExpr'), g, f, b, a, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], dep)
    | .UV {V, hUV, g, fEqg, b, aEqb, ..} => 
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (#[A.toExpr, V, U, (← if dep then hUV.toExprDep' else hUV.toExpr'), g, f, b, a, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], dep)
    | .UVFun {V, hUV, g, fEqg, ..} => 
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (#[A.toExpr, V, U, (← if dep then hUV.toExprDep' else hUV.toExpr'), g, f, a, (← fEqg.1.toExpr')], dep)
    | .AB {B, hAB, g, fEqg, b, aEqb, ..} => 
      let U := U.1
      pure (#[B.toExpr, A, U, (← hAB.1.toExpr'), g, f, b, a, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], false)
    | .none {g, fEqg, b, aEqb, ..} => -- TODO fails to show termination if doing nested match?
      let (U, dep) ← getMaybeDepLemmaApp1 U
      pure (#[A.toExpr, U, g, f, b, a, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], dep)
    | .Fun {g, fEqg, ..} =>
      let (U, dep) ← getMaybeDepLemmaApp1 U
      pure (#[A.toExpr, U, g, f, a, (← fEqg.1.toExpr')], dep)
    | .Arg {b, aEqb, ..} =>
      let (U, dep) ← getMaybeDepLemmaApp1 U
      pure (#[A.toExpr, U, f, b, a, (← aEqb.1.toExpr')], dep)
  else
    match extra with
    | .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb, ..} =>
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (#[A.toExpr, B, U, V, (← hAB.1.toExpr'), (← if dep then do hUV.toExprDep' else hUV.toExpr'), f, g, a, b, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], dep)
    | .UV {V, hUV, g, fEqg, b, aEqb, ..} => 
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (#[A.toExpr, U, V, (← if dep then hUV.toExprDep' else hUV.toExpr'), f, g, a, b, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], dep)
    | .UVFun {V, hUV, g, fEqg, ..} => 
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (#[A.toExpr, U, V, (← if dep then hUV.toExprDep' else hUV.toExpr'), f, g, a, (← fEqg.1.toExpr')], dep)
    | .AB {B, hAB, g, fEqg, b, aEqb, ..} => 
      let U := U.1
      pure (#[A.toExpr, B, U, (← hAB.1.toExpr'), f, g, a, b, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], false)
    | .none {g, fEqg, b, aEqb, ..} => -- TODO fails to show termination if doing nested match?
      let (U, dep) ← getMaybeDepLemmaApp1 U
      pure (#[A.toExpr, U, f, g, a, b, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], dep)
    | .Fun {g, fEqg, ..} =>
      let (U, dep) ← getMaybeDepLemmaApp1 U
      pure (#[A.toExpr, U, f, g, a, (← fEqg.1.toExpr')], dep)
    | .Arg {b, aEqb, ..} =>
      let (U, dep) ← getMaybeDepLemmaApp1 U
      pure (#[A.toExpr, U, f, a, b, (← aEqb.1.toExpr')], dep)
  let n := extra.lemmaName dep
  pure $ Lean.mkAppN (.const n [u, v]) args

def TransData.toExpr (e : TransData EExpr) : EM Expr := match e with
| {u, A, B, C, a, b, c, aEqb, bEqc, ..} => do
  if (← rev) then
    pure $ Lean.mkAppN (.const `HEq.trans [u]) #[C, B, A, c, b, a, (← bEqc.1.toExpr'), (← aEqb.1.toExpr') ]
  else
    pure $ Lean.mkAppN (.const `HEq.trans [u]) #[A, B, C, a, b, c, (← aEqb.1.toExpr'), (← bEqc.1.toExpr')]

-- def SymmData.toExpr (e : SymmData EExpr) : EM Expr := do match e with
-- | {u, A, B, a, b, aEqb} =>
--   if (← rev) then
--     swapRev aEqb.toExpr'
--   else
--     pure $ Lean.mkAppN (.const `HEq.symm [u]) #[A, B, a, b, (← aEqb.toExpr')]

def ReflData.toExpr : ReflData → EM Expr
| {u, A, a} => pure $ Lean.mkAppN (.const `L4L.HEqRefl [u]) #[A, a]

def PIData.toExpr (e : PIData EExpr) : EM Expr := match e with
| {P, p, q, extra, ..} => do
  if (← rev) then
    match extra with
    | .none =>
      pure $ Lean.mkAppN (.const `L4L.prfIrrelHEq []) #[P, q, p]
    | .HEq {Q, hPQ, ..} =>
      pure $ Lean.mkAppN (.const `L4L.prfIrrelHEqPQ []) #[Q, P, (← hPQ.1.toExpr'), q, p]
  else
    match extra with
    | .none =>
      pure $ Lean.mkAppN (.const `L4L.prfIrrelHEq []) #[P, p, q]
    | .HEq {Q, hPQ, ..} =>
      pure $ Lean.mkAppN (.const `L4L.prfIrrelHEqPQ []) #[P, Q, (← hPQ.1.toExpr'), p, q]

def FVarDataE.toExpr : FVarDataE → EM Expr
| {aEqb, bEqa, u, A, B, a, b, ..} => do
  if (← rev) then
    if (← read).reversedFvars.contains aEqb then
      pure bEqa.toExpr
    else
      pure $ Lean.mkAppN (.const `HEq.symm [u]) #[A, B, a, b, aEqb.toExpr]
  else
    if (← read).reversedFvars.contains aEqb then
      pure $ Lean.mkAppN (.const `HEq.symm [u]) #[B, A, b, a, bEqa.toExpr]
    else
      pure aEqb.toExpr

def LVarDataE.toExpr : LVarDataE → EM Expr
| e@({v, u, A, B, a, b, ..}) => do
  if (← rev) then
    if (← read).reversedFvars.contains v then
      pure $ .fvar v
    else
      pure $ Lean.mkAppN (.const `HEq.symm [u]) #[A, B, a, b, .fvar v]
  else
    if (← read).reversedFvars.contains v then
      pure $ Lean.mkAppN (.const `HEq.symm [u]) #[B, A, b, a, .fvar v]
    else
      pure $ .fvar v

def SorryData.toExpr : SorryData → EM Expr
| {u, A, a, B, b} => do
  if (← rev) then
    pure $ Lean.mkAppN (.const `sorryAx [0]) #[Lean.mkAppN (.const ``HEq [u]) #[B, b, A, a], .const `Bool.false []]
  else
    pure $ Lean.mkAppN (.const `sorryAx [0]) #[Lean.mkAppN (.const ``HEq [u]) #[A, a, B, b], .const `Bool.false []]

def UnitEtaData.toExpr : UnitEtaData → EM Expr
| {u, A, a, b, proof} => do
  -- `proof : HEq a b`; emit it directly (or its symm under reversal).
  if (← rev) then
    pure $ Lean.mkAppN (.const ``HEq.symm [u]) #[A, A, a, b, proof]
  else
    pure proof.toExpr

def CastData.toExpr : CastData EExpr → EM Expr
| {u, A, B, e, p} => do
  if (← rev) then
    pure $ Lean.mkAppN (.const `L4L.castOrigHEqSymm [u]) #[A, B, ← (swapRev p.toExpr'),  e]
  else
    pure $ Lean.mkAppN (.const `L4L.castOrigHEq [u]) #[A, B, ← p.toExpr',  e]

def EExpr.ctorName : EExpr → Name 
  | .lam .. => `lam
  | .forallE .. => `forallE
  | .app .. => `app
  | .fvar .. => `fvar
  | .lvar .. => `lvar
  | .trans .. => `trans
  | .refl .. => `refl
  | .prfIrrel .. => `prfIrrel
  | .sry .. => `sry
  | .unitEta .. => `unitEta
  | .cast .. => `cast
  | .rev .. => `rev

def withCtorName (n : Name × Array Name) (m : EM T) : EM T := do
  withReader (fun ctx => {ctx with ctorStack := ctx.ctorStack.push n}) m

def EExpr.toExpr' (e : EExpr) : EM Expr := 
  withCtorName (e.ctorName, e.usedLets.toArray.map (·.name)) do
  let ret ← match e with
  | .lam d
  | .forallE d
  | .app d
  | .fvar d
  | .lvar d
  | .trans d
  | .refl d
  | .prfIrrel d
  | .sry d
  | .unitEta d
  | .cast d => d.toExpr
  | .rev e => do
    let ret ← (swapRev e.toExpr')
    pure ret
  pure ret

-- def EExpr.toSorry (e : EExpr) : EExpr :=
--   match e with
--   | .other l T S t s _ => .sry {u := l, A := T, B := S, a := t, b := s}
--   | .lam d => .sry {u := .ima, A := T, B := S, a := t, b := s}
--   | .forallE d
--   | .app d
--   | .fvar d
--   | .trans d
--   -- | .symm d
--   | .refl d
--   | .prfIrrel d
--   | .sry d  => d.toExpr
--   -- | .rev .. => panic! "encountered thunked reversal"
--   | .rev e => sorry


end

def EExpr.toExpr (e : EExpr) (dbg := false) : Expr := Id.run $ do
  -- dbg_trace s!"DBG[1]: EExpr.lean:1066 (after def EExpr.toExpr (e : EExpr) (dbg := fal…)"
  let ret ← e.toExpr'.run dbg
  -- dbg_trace s!"DBG[2]: EExpr.lean:1068 (after let ret ← e.toExpr.run dbg)"
  pure ret

namespace EExpr

def toPExpr (e : EExpr) : PExpr := .mk e.toExpr

-- instance : BEq EExpr where
-- beq x y := x.toExpr == y.toExpr

end EExpr

instance : ToString EExpr where
toString e := toString $ e.toExpr default

-- def EExpr.instantiateRev (e : EExpr) (subst : Array EExpr) : EExpr :=
--   e.toExpr.instantiateRev (subst.map (·.toExpr)) |>.toEExpr

instance : ToString (Option EExpr) where
toString e? := toString $ e?.map (·.toExpr default)

-- instance : Coe EExpr Expr := ⟨toExpr⟩
-- instance : Coe EExpr PExpr := ⟨(EExpr.toPExpr default)⟩

structure BinderData where
name : Name
dom : PExpr
info : BinderInfo
deriving Inhabited

end Lean4Less
