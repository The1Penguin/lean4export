import Lean

open Lean

instance : ToJson BinderInfo where
  toJson
  | .default        => .str "default"
  | .implicit       => .str "implicit"
  | .strictImplicit => .str "strictImplicit"
  | .instImplicit   => .str "instImplicit"

instance : ToJson Literal where
  toJson
  | .natVal val => .num val
  | .strVal val => .str val

instance : ToJson QuotKind where
  toJson
  | .type => .str "type"
  | .ctor => .str "ctor"
  | .lift => .str "lift"
  | .ind  => .str "ind"

instance : ToJson MData where
  toJson
  | _k => .null -- TODO: Complains with the following message
  -- elaboration function for 'term.pseudo.antiquot' has not been implemented $k.entries

partial def Level.toJson : Level -> Json
  | .zero         => .num 0
  | .succ l       =>
    have : ToJson Level := ⟨Level.toJson⟩
    json% { "succ" : $l }
  | .max n m      =>
    have : ToJson Level := ⟨Level.toJson⟩
    json% { "max" : [$n,$m] }
  | .imax n m     =>
    have : ToJson Level := ⟨Level.toJson⟩
    json% { "imax" : [$n,$m] }
  | .param name   => json% { "param" : $name }
  | .mvar LMVarId => json% { "lmVarId" : $LMVarId.name }
instance : ToJson Level := ⟨Level.toJson⟩

partial def Expr.toJson : Expr -> Json
  | .bvar (deBruijnIndex : Nat) => json% { "bVar" : { "index" : $deBruijnIndex } }
  | .fvar (fvarId : FVarId) => json% { "fVar" : { "id" : $fvarId.name }}
  | .mvar (mvarId : MVarId) => json% { "mVar" : { "id" : $mvarId.name }}
  | .sort (u : Level) => json% { "sort" : { "level" : $u }}
  | .const (declName : Name) (us : List Level) => json% { "const" : {"declName" : $declName, "levels" : $us }}
  | .app (fn : Expr) (arg : Expr) =>
      have : ToJson Expr := ⟨Expr.toJson⟩
      json% { "app" : { "fn" : $fn, "arg" : $arg }}
  | .lam (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo) =>
      have : ToJson Expr := ⟨Expr.toJson⟩
      json% { "lambda" : { "binderName" : $binderName, "binderType" : $binderType, "body" : $body, "binderInfo" : $binderInfo} }
  | .forallE (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo) =>
      have : ToJson Expr := ⟨Expr.toJson⟩
      json% { "forAllE" : { "binderName" : $binderName, "binderType" : $binderType, "body" : $body, "binderInfo" : $binderInfo} }
  | .letE (declName : Name) (type : Expr) (value : Expr) (body : Expr) (nonDep : Bool) =>
      have : ToJson Expr := ⟨Expr.toJson⟩
      json% { "letE" : { "declName" : $declName, "type" : $type, "value" : $value, "body" : $body, "nonDep" : $nonDep} }
  | .lit (l : Literal)  => json% { "literal" : $l }
  | .mdata (data : MData) (expr : Expr) =>
      have : ToJson Expr := ⟨Expr.toJson⟩
      json% { "mData" : { "data" : $data, "expr" : $expr }}
  | .proj (typeName : Name) (idx : Nat) (struct : Expr) =>
      have : ToJson Expr := ⟨Expr.toJson⟩
      json% { "proj" : { "typeName" : $typeName, "idx" : $idx, "struct" : $struct } }

instance : ToJson Expr := ⟨Expr.toJson⟩


instance : ToJson AxiomVal := ⟨λ s => json% { "name" : $s.name, "type" : $s.type}⟩
instance : ToJson DefinitionVal := ⟨λ s => json% { "name" : $s.name, "type" : $s.type, "val" : $s.value } ⟩
instance : ToJson TheoremVal := ⟨λ s => json% { "name" : $s.name, "type" : $s.type, "val" : $s.value}⟩
instance : ToJson OpaqueVal := ⟨λ s => json% { "name" : $s.name, "type" : $s.type, "val" : $s.value}⟩
instance : ToJson QuotVal := ⟨λ s => json% { "name" : $s.name, "type" : $s.type, "kind" : $s.kind}⟩
instance : ToJson InductiveVal := ⟨λ s => json% { "name" : $s.name, "type" : $s.type, "ctors" : $s.ctors}⟩
instance : ToJson ConstructorVal := ⟨λ s => json% { "name" : $s.name, "type" : $s.type}⟩
instance : ToJson RecursorVal := ⟨λ s => json% { "name" : $s.name, "type" : $s.type}⟩

instance : ToJson (Name × ConstantInfo) where
  toJson
    | (n, .axiomInfo  v) => json% { "name" : $n, "axiomVal" : $v}
    | (n, .defnInfo   v) => json% { "name" : $n, "definitionalVal" : $v}
    | (n, .thmInfo    v) => json% { "name" : $n, "theoremVal" : $v}
    | (n, .opaqueInfo v) => json% { "name" : $n, "opaqueVal" : $v}
    | (n, .quotInfo   v) => json% { "name" : $n, "quotVal" : $v}
    | (n, .inductInfo v) => json% { "name" : $n, "inductiveVal" : $v}
    | (n, .ctorInfo   v) => json% { "name" : $n, "constructorVal" : $v}
    | (n, .recInfo    v) => json% { "name" : $n, "recursorVal" : $v}

instance : Hashable RecursorRule where
  hash r := hash (r.ctor, r.nfields, r.rhs)

structure Context where
  env : Environment

structure State where
  visitedNames : HashMap Name Nat := .insert {} .anonymous 0
  visitedLevels : HashMap Level Nat := .insert {} .zero 0
  visitedExprs : HashMap Expr Nat := {}
  visitedRecRules : HashMap RecursorRule Nat := {}
  visitedConstants : NameHashSet := {}

abbrev M := ReaderT Context <| StateT State IO

def M.run (env : Environment) (act : M α) : IO α :=
  StateT.run' (s := {}) do
    ReaderT.run (r := { env }) do
      act

partial def dumpConstant (c : Name) : M (List Json) := do
  if (← get).visitedConstants.contains c then
    return .nil
  modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
  match (← read).env.find? c |>.get! with
  | .axiomInfo val => do
    if val.isUnsafe then
      return .nil
    return [(toJson (c, Lean.ConstantInfo.axiomInfo val) )]
  | .defnInfo val => do
    if val.safety != .safe then
      return .nil
    return [(toJson (c, Lean.ConstantInfo.defnInfo val) )]
  | .thmInfo val => do
    return [(toJson (c, Lean.ConstantInfo.thmInfo val) )]
  | .opaqueInfo val => do
    if val.isUnsafe then
      return .nil
    return [(toJson (c, Lean.ConstantInfo.opaqueInfo val) )]
  | .quotInfo val =>
    return [(toJson (c, Lean.ConstantInfo.quotInfo val) )]
  | .inductInfo val => do
    if val.isUnsafe then
      return .nil
    let mut n := []
    for ctor in val.ctors do
      let d <- dumpConstant ( (← read).env.find? ctor |>.get!.name)
      n := List.append d n
    let temp := toJson (c, Lean.ConstantInfo.inductInfo val)
    let new := match temp.getObjVal? "inductiveVal" with
                  | .ok j => j.setObjVal! "ctors" (toJson n)
                  | .error _ => sorry
    return [temp.setObjVal! "inductiveVal" new ]
  | .ctorInfo val =>
    if val.isUnsafe then
      return .nil
    return [(toJson (c, Lean.ConstantInfo.ctorInfo val) )]
  | .recInfo val =>
    if val.isUnsafe then
      return .nil
    return [(toJson (c, Lean.ConstantInfo.recInfo val))]
