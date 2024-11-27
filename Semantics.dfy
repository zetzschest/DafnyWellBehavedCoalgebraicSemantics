include "Expressions.dfy"
include "Languages.dfy"

module Semantics {

  import opened Expressions
  import opened Languages

  /* Definitions */

  /* Denotational Semantics */

  function Denotational<A(==)>(e: Exp): Lang {
    match e
    case Zero => Languages.Zero()
    case One => Languages.One()
    case Char(a) => Languages.Singleton(a)
    case Plus(e1, e2) => Languages.Plus(Denotational(e1), Denotational(e2))
    case Comp(e1, e2) => Languages.Comp(Denotational(e1), Denotational(e2))
    case Star(e1) => Languages.Star(Denotational(e1))
  }

  /* Operational Semantics */

  function Operational<A(==)>(e: Exp): Lang {
    Alpha(Eps(e), (a: A) => Operational(Delta(e)(a)))
  }

  /* (Co)algebra homomorphisms f: Exp -> Lang */

  ghost predicate IsCoalgebraHomomorphism<A(!new)>(f: Exp -> Lang) {
    && (forall e :: f(e).eps == Eps(e))
    && (forall e, a :: Bisimilar(f(e).delta(a), f(Delta(e)(a))))
  }

  ghost predicate IsAlgebraHomomorphism<A(!new)>(f: Exp -> Lang) {
    forall e :: IsAlgebraHomomorphismPointwise(f, e)
  }

  ghost predicate IsAlgebraHomomorphismPointwise<A(!new)>(f: Exp -> Lang, e: Exp) {
    Bisimilar<A>(
      f(e),
      match e
      case Zero => Languages.Zero()
      case One => Languages.One()
      case Char(a) => Languages.Singleton(a)
      case Plus(e1, e2) => Languages.Plus(f(e1), f(e2))
      case Comp(e1, e2) => Languages.Comp(f(e1), f(e2))
      case Star(e1) => Languages.Star(f(e1))
    )
  }

  /* Lemmas */

  /* Any two coalgebra homomorphisms f,g: Exp -> Lang are equal up to bisimulation */

  lemma UniqueCoalgebraHomomorphism<A(!new)>(f: Exp -> Lang, g: Exp -> Lang, e: Exp)
    requires IsCoalgebraHomomorphism(f)
    requires IsCoalgebraHomomorphism(g)
    ensures Bisimilar(f(e), g(e))
  {
    BisimilarityIsReflexive(f(e));
    BisimilarityIsReflexive(g(e));
    UniqueCoalgebraHomomorphismHelper(f, g, f(e), g(e));
  }

  lemma UniqueCoalgebraHomomorphismHelper<A(!new)>(f: Exp -> Lang, g: Exp -> Lang, L1: Lang, L2: Lang)
    requires IsCoalgebraHomomorphism(f)
    requires IsCoalgebraHomomorphism(g)
    requires exists e :: Bisimilar(L1, f(e)) && Bisimilar(L2, g(e))
    ensures Bisimilar(L1, L2)
  {
    forall k: nat
      ensures Bisimilar#[k](L1, L2)
    {
      if k != 0 {
        UniqueCoalgebraHomomorphismHelperPointwise(k, f, g, L1, L2);
      }
    }
  }

  lemma UniqueCoalgebraHomomorphismHelperPointwise<A(!new)>(k: nat, f: Exp -> Lang, g: Exp -> Lang, L1: Lang, L2: Lang)
    requires IsCoalgebraHomomorphism(f)
    requires IsCoalgebraHomomorphism(g)
    requires exists e :: Bisimilar#[k](L1, f(e)) && Bisimilar#[k](L2, g(e))
    ensures Bisimilar#[k](L1, L2)
  {
    var e :| Bisimilar#[k](L1, f(e)) && Bisimilar#[k](L2, g(e));
    if k != 0 {
      forall a
        ensures Bisimilar#[k-1](L1.delta(a), L2.delta(a))
      {
        BisimilarityIsTransitivePointwise(k-1, L1.delta(a),  f(e).delta(a), f(Delta(e)(a)));
        BisimilarityIsTransitivePointwise(k-1, L2.delta(a),  g(e).delta(a), g(Delta(e)(a)));
        UniqueCoalgebraHomomorphismHelperPointwise(k-1, f, g, L1.delta(a), L2.delta(a));
      }
    }
  }

  /* Denotational is an algebra homomorphism */

  lemma DenotationalIsAlgebraHomomorphism<A(!new)>()
    ensures IsAlgebraHomomorphism<A>(Denotational)
  {
    forall e
      ensures IsAlgebraHomomorphismPointwise<A>(Denotational, e)
    {
      BisimilarityIsReflexive<A>(Denotational(e));
    }
  }

  /* Denotational is a coalgebra homomorphism */

  lemma DenotationalIsCoalgebraHomomorphism<A(!new)>()
    ensures IsCoalgebraHomomorphism<A>(Denotational)
  {
    forall e
      ensures Denotational<A>(e).eps == Eps(e)
    {
      DenotationalIsCoalgebraHomomorphismHelper1(e);
    }
    forall e, a
      ensures Bisimilar(Denotational<A>(e).delta(a), Denotational<A>(Delta(e)(a)))
    {
      DenotationalIsCoalgebraHomomorphismHelper2(e, a);
    }
  }

  lemma DenotationalIsCoalgebraHomomorphismHelper1<A>(e: Exp)
    ensures Denotational<A>(e).eps == Eps(e)
  {
    match e
    case Zero =>
    case One =>
    case Char(a) =>
    case Plus(e1, e2) =>
      DenotationalIsCoalgebraHomomorphismHelper1(e1);
      DenotationalIsCoalgebraHomomorphismHelper1(e2);
    case Comp(e1, e2) =>
      DenotationalIsCoalgebraHomomorphismHelper1(e1);
      DenotationalIsCoalgebraHomomorphismHelper1(e2);
    case Star(e1) =>
      DenotationalIsCoalgebraHomomorphismHelper1(e1);
  }

  lemma DenotationalIsCoalgebraHomomorphismHelper2<A(!new)>(e: Exp, a: A)
    ensures Bisimilar(Denotational<A>(e).delta(a), Denotational<A>(Delta(e)(a)))
  {
    match e
    case Zero => BisimilarityIsReflexive<A>(Languages.Zero());
    case One => BisimilarityIsReflexive<A>(Languages.One());
    case Char(b) =>
      if a == b {
        BisimilarityIsReflexive<A>(Languages.One());
      } else {
        BisimilarityIsReflexive<A>(Languages.Zero());
      }
    case Plus(e1, e2) =>
      DenotationalIsCoalgebraHomomorphismHelper2(e1, a);
      DenotationalIsCoalgebraHomomorphismHelper2(e2, a);
      PlusCongruence(Denotational(e1).delta(a), Denotational(Delta(e1)(a)), Denotational(e2).delta(a), Denotational(Delta(e2)(a)));
    case Comp(e1, e2) =>
      DenotationalIsCoalgebraHomomorphismHelper1(e1);
      DenotationalIsCoalgebraHomomorphismHelper2(e1, a);
      DenotationalIsCoalgebraHomomorphismHelper2(e2, a);
      BisimilarityIsReflexive<A>(Denotational(e2));
      BisimilarityIsReflexive<A>(if Eps(e1) then Languages.One() else Languages.Zero());
      CompCongruence(
        Denotational(e1).delta(a),
        Denotational(Delta(e1)(a)),
        Denotational(e2),
        Denotational(e2)
      );
      CompCongruence(
        if Eps(e1) then Languages.One() else Languages.Zero(),
        if Eps(e1) then Languages.One() else Languages.Zero(),
        Denotational(e2).delta(a),
        Denotational(Delta(e2)(a))
      );
      PlusCongruence(
        Languages.Comp(Denotational(e1).delta(a), Denotational(e2)),
        Languages.Comp(Denotational(Delta(e1)(a)), Denotational(e2)),
        Languages.Comp(if Eps(e1) then Languages.One() else Languages.Zero(), Denotational(e2).delta(a)),
        Languages.Comp(if Eps(e1) then Languages.One() else Languages.Zero(), Denotational(Delta(e2)(a)))
      );
    case Star(e1) =>
      DenotationalIsCoalgebraHomomorphismHelper2(e1, a);
      BisimilarityIsReflexive(Languages.Star(Denotational(e1)));
      CompCongruence(Denotational(e1).delta(a), Denotational(Delta(e1)(a)), Languages.Star(Denotational(e1)), Languages.Star(Denotational(e1)));
  }

  /* Operational is an algebra homomorphism */

  lemma OperationalIsAlgebraHomomorphism<A(!new)>()
    ensures IsAlgebraHomomorphism<A>(Operational)
  {
    forall e 
      ensures IsAlgebraHomomorphismPointwise<A>(Operational, e) 
    {
      OperationalAndDenotationalAreBisimilar<A>(e);
      assert IsAlgebraHomomorphismPointwise(Denotational, e) by {
        DenotationalIsAlgebraHomomorphism<A>();
      }
      match e
      case Zero =>
        BisimilarityIsTransitive(Operational<A>(Zero), Denotational<A>(Zero), Languages.Zero());
      case One =>
        BisimilarityIsTransitive(Operational<A>(One), Denotational<A>(One), Languages.One());
      case Char(a) =>
        BisimilarityIsTransitive(Operational<A>(Char(a)), Denotational<A>(Char(a)), Languages.Singleton(a));
      case Plus(e1, e2) =>
        BisimilarityIsTransitive(Operational<A>(Plus(e1, e2)), Denotational<A>(Plus(e1, e2)), Languages.Plus(Denotational(e1), Denotational(e2)));
        OperationalAndDenotationalAreBisimilar(e1);
        BisimilarityIsSymmetric(Denotational(e1), Operational(e1));
        OperationalAndDenotationalAreBisimilar(e2);
        BisimilarityIsSymmetric(Denotational(e2), Operational(e2));
        PlusCongruence<A>(Denotational(e1), Operational(e1), Denotational(e2), Operational(e2));
        BisimilarityIsTransitive(Operational<A>(Plus(e1, e2)), Languages.Plus(Denotational(e1), Denotational(e2)), Languages.Plus(Operational(e1), Operational(e2)));
      case Comp(e1, e2) =>
        BisimilarityIsTransitive(Operational<A>(Comp(e1, e2)), Denotational<A>(Comp(e1, e2)), Languages.Comp(Denotational(e1), Denotational(e2)));
        OperationalAndDenotationalAreBisimilar(e1);
        BisimilarityIsSymmetric(Denotational(e1), Operational(e1));
        OperationalAndDenotationalAreBisimilar(e2);
        BisimilarityIsSymmetric(Denotational(e2), Operational(e2));
        CompCongruence<A>(Denotational(e1), Operational(e1), Denotational(e2), Operational(e2));
        BisimilarityIsTransitive(Operational<A>(Comp(e1, e2)), Languages.Comp(Denotational(e1), Denotational(e2)), Languages.Comp(Operational(e1), Operational(e2)));
      case Star(e1) =>
        BisimilarityIsTransitive(Operational<A>(Star(e1)), Denotational<A>(Star(e1)), Languages.Star(Denotational(e1)));
        OperationalAndDenotationalAreBisimilar(e1);
        BisimilarityIsSymmetric(Denotational(e1), Operational(e1));
        StarCongruence(Denotational(e1), Operational(e1));
        BisimilarityIsTransitive(Operational<A>(Star(e1)), Languages.Star(Denotational(e1)), Languages.Star(Operational(e1)));
    }
  }

  /* Operational is a coalgebra homomorphism */

  lemma OperationalIsCoalgebraHomomorphism<A(!new)>()
    ensures IsCoalgebraHomomorphism<A>(Operational)
  {
    forall e, a
      ensures Bisimilar<A>(Operational(e).delta(a), Operational(Delta(e)(a)))
    {
      BisimilarityIsReflexive(Operational(e).delta(a));
    }
  }

  /* Operational and Denotational are equal, up to bisimulation */

  lemma OperationalAndDenotationalAreBisimilar<A(!new)>(e: Exp)
    ensures Bisimilar<A>(Operational(e), Denotational(e))
  {
    OperationalIsCoalgebraHomomorphism<A>();
    DenotationalIsCoalgebraHomomorphism<A>();
    UniqueCoalgebraHomomorphism<A>(Operational, Denotational, e);
  }

}
