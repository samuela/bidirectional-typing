# Homemade Bidirectional Typing

```
(λ f. (λ g. (λ x. f (g x))))
=> ((a -> b) -> ((c -> a) -> (c -> b)))
```

A bidirectional type inference system loosely based on [Complete and Easy Bidirectional Typechecking
for Higher-Rank Polymorphism]( https://www.cs.cmu.edu/~joshuad/papers/bidir/Dunfield13_bidir_submitted.pdf).

I read a bit about bidirectional type inference about a year ago but was fuzzy on many of the details, so I figured that it would be a fun exercise to try to implement a full type inference and checking algorithm without consulting any references. This is the result.

# Exposition

At the core is a small lambda calculus,

```haskell
data Expr =
    EUnit Loc
  | EIdent Loc Id
  | EAnno Loc Expr Type
  | ELam Loc Id Expr
  | EApp Loc Expr Expr
```

featuring a unit type which is simply a base type but without anything interesting that you can do with it. `Loc` here refers to a type which specifies source location of the expression. After all, two variables with the same name in different parts of the program are unique and need not have the same type.

A corresponding interpreter is included as well,

```haskell
data Val =
    VUnit
  | VLam Env Id Expr

type Env = Map Id Val

interp :: Env -> Expr -> Maybe Val
interp _ (EUnit _) = Just VUnit
interp env (EIdent _ x) = Map.lookup x env
interp env (EAnno _ body _) = interp env body
interp env (ELam _ x body) = Just (VLam env x body)
interp env (EApp _ f a) = case ((interp env f), (interp env a)) of
  (Just (VLam fenv y body), Just xval) -> interp (Map.insert y xval fenv) body
  otherwise -> Nothing

run :: Expr -> Maybe Val
run = interp Map.empty
```

Moving along...

# Type Inference

This is the fun part. Bidirectional typing is centered on two operations, hence the name.

* Type **checking**, checking that an expression satisfies a given type under some context. For example, checking that `(λ x. x)` has type `a -> a` should succeed but checking it against the unit type should fail.
* Type **synthesis**, given an expression and some program context synthesize a new type for the expression. We may not have enough information to determine the exact type that the expression must have, but we can make a guess and put in some placeholders where necessary. For example, we know `(λ x. <body>)` must have a function type `a -> b`, but we can't quite be sure about what `a` and `b` are without looking into the body of the lambda.

Since I was starting with very few pre-conceived notions about what a bidirectional type inference algorithm should look like I ended up diverging from the "Complete and Easy" algorithm in a few ways. In particular, instead of maintaining a so-called "ordered algorithmic context" I simply maintained type environment that mapped source expressions to `TypeId`s which are then mapped to types:

```haskell
newtype TypeId = TypeId Integer

data Type =
    TUnit
  | TIdent TypeId
  | TLam Type Type

data TypeStatus =
    Exists
  | Forall
  | Typed Type

data TypeEnv = TypeEnv Integer (Map Expr TypeId) (Map TypeId TypeStatus)
```

Well, it's a little bit more complicated than that: a `TypeId` can also be marked as existential (`Exists`), meaning that we have not yet determined what it should be, or universal (`Forall`), meaning that it is a type variable in some polymorphic type. The added indirection here is necessary to model the fact that multiple source expressions may map to the same type. It also allows types to reference other types via `TIdent`s. We also keep an `Integer` around so we know what the next unused `TypeId` should be.

Another distinction is that I managed to reduce the checking half of bidirectional typing to simply a synthesis, followed by a subtype operation:

```haskell
check :: TypeEnv -> Expr -> Type -> Maybe TypeEnv
check tenv expr typ = do
  (typ', tenv') <- synth tenv expr
  tenv'' <- subtype tenv' typ' typ
  return tenv''
```

I'm not sure if this is a good or bad thing really. I view it as a simplification, personally. (This is equivalent to the Sub rule in "Complete and Easy.")

The rest of the implementation actually reflects the "Complete and Easy" algorithm fairly closely. I also ended up with `subtype` and `synth`, but happened to inline the instantiation rules.

```haskell
synth :: TypeEnv -> Expr -> Maybe (Type, TypeEnv)

subtype :: TypeEnv -> Type -> Type -> Maybe TypeEnv
```

These implementations are fairly routine. Function applications are a little tricky, but with those figured out the rest falls into place. Function subtyping also requires a little bit of care, of course. `A1 <: A2` and `B1 <: B2` does not imply `A1 -> B1 <: A2 -> B2`!

All in all, I'm pretty happy with the way it turned out. In my (very partial) opinion, the implementation with an unordered mapping from expressions to types is more intuitive than thinking about an ordered context of solved and unsolved types. The implementation also doesn't require type markers or list splicing kung fu which is nice.

I went back to read the paper and noted the connections between the two in code comments so it should be fairly approachable to readers who prefer reading at LaTeX.

# TODO
* There are a number of things that could be made more monadic/clean. PRs welcome!
* Record subtyping is next on my list. I spent a bit of time on this, but I've come to the conclusion that it requires using a constraint solver approach. Should be do-able though.
