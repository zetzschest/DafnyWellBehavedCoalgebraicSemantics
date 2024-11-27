module Languages {

  /* Definitions */

  codatatype Lang<!A> = Alpha(eps: bool, delta: A -> Lang<A>)

  function Zero<A>(): Lang {
    Alpha(false, (a: A) => Zero())
  }

  function One<A>(): Lang {
    Alpha(true, (a: A) => Zero())
  }

  function Singleton<A(==)>(a: A): Lang {
    Alpha(false, (b: A) => if a == b then One() else Zero())
  }

  function {:abstemious} Plus<A>(L1: Lang, L2: Lang): Lang {
    Alpha(L1.eps || L2.eps, (a: A) => Plus(L1.delta(a), L2.delta(a)))
  }

  function {:abstemious} Comp<A>(L1: Lang, L2: Lang): Lang {
    Alpha(L1.eps && L2.eps, (a: A) => Plus(Comp(L1.delta(a), L2), Comp(if L1.eps then One() else Zero(), L2.delta(a))))
  }

  function Star<A>(L: Lang): Lang {
    Alpha(true, (a: A) => Comp(L.delta(a), Star(L)))
  }

  greatest predicate Bisimilar<A(!new)>[nat](L1: Lang, L2: Lang) {
    && (L1.eps == L2.eps)
    && (forall a :: Bisimilar(L1.delta(a), L2.delta(a)))
  }

  /* Lemmas */

  /* Bisimilarity */

  greatest lemma BisimilarityIsReflexive<A(!new)>[nat](L: Lang)
    ensures Bisimilar(L, L)
  {}

  lemma BisimilarityIsTransitiveAlternative<A(!new)>(L1: Lang, L2: Lang, L3: Lang)
    ensures Bisimilar(L1, L2) && Bisimilar(L2, L3) ==> Bisimilar(L1, L3)
  {
    if Bisimilar(L1,L2) && Bisimilar(L2, L3) {
      assert Bisimilar(L1, L3) by {
        BisimilarityIsTransitive(L1, L2, L3);
      }
    }
  }

  greatest lemma BisimilarityIsTransitive<A(!new)>[nat](L1: Lang, L2: Lang, L3: Lang)
    requires Bisimilar(L1, L2) && Bisimilar(L2, L3)
    ensures Bisimilar(L1, L3)
  {}

  lemma BisimilarityIsTransitivePointwise<A(!new)>(k: nat, L1: Lang, L2: Lang, L3: Lang)
    ensures Bisimilar#[k](L1, L2) && Bisimilar#[k](L2, L3) ==> Bisimilar#[k](L1, L3)
  {
    if k != 0 {
      if Bisimilar#[k](L1, L2) && Bisimilar#[k](L2, L3) {
        assert Bisimilar#[k](L1, L3) by {
          forall a
            ensures Bisimilar#[k-1](L1.delta(a), L3.delta(a))
          {
            BisimilarityIsTransitivePointwise(k-1, L1.delta(a), L2.delta(a), L3.delta(a));
          }
        }
      }
    }
  }

  greatest lemma BisimilarityIsSymmetric<A(!new)>[nat](L1: Lang, L2: Lang)
    ensures Bisimilar(L1, L2) ==> Bisimilar(L2, L1)
    ensures Bisimilar(L1, L2) <== Bisimilar(L2, L1)
  {}

  lemma BisimilarCuttingPrefixes<A(!new)>(k: nat, L1: Lang, L2: Lang)
    requires forall n: nat :: n <= k + 1 ==> Bisimilar#[n](L1, L2)
    ensures forall a :: Bisimilar#[k](L1.delta(a), L2.delta(a))
  {
    forall a
      ensures Bisimilar#[k](L1.delta(a), L2.delta(a))
    {
      if k != 0 {
        assert Bisimilar#[k + 1](L1, L2);
      }
    }
  }

  lemma BisimilarCuttingPrefixesPointwise<A(!new)>(k: nat, a: A, L1a: Lang, L1b: Lang)
    requires k != 0
    requires forall n: nat :: n <= k + 1 ==> Bisimilar#[n](L1a, L1b)
    ensures forall n: nat :: n <= k ==> Bisimilar#[n](L1a.delta(a), L1b.delta(a))
  {
    forall n: nat
      ensures n <= k ==> Bisimilar#[n](L1a.delta(a), L1b.delta(a))
    {
      if n <= k {
        BisimilarCuttingPrefixes(n, L1a, L1b);
      }
    }
  }

  /* Congruence of Plus */

  greatest lemma PlusCongruence<A(!new)>[nat](L1a: Lang, L1b: Lang, L2a: Lang, L2b: Lang)
    requires Bisimilar(L1a, L1b)
    requires Bisimilar(L2a, L2b)
    ensures Bisimilar(Plus(L1a, L2a), Plus(L1b, L2b))
  {}

  lemma PlusCongruenceAlternative<A(!new)>(k: nat, L1a: Lang, L1b: Lang, L2a: Lang, L2b: Lang)
    requires Bisimilar#[k](L1a, L1b)
    requires Bisimilar#[k](L2a, L2b)
    ensures Bisimilar#[k](Plus(L1a, L2a), Plus(L1b, L2b))
  {}

  /* Congruence of Comp */

  lemma CompCongruence<A(!new)>(L1a: Lang, L1b: Lang, L2a: Lang, L2b: Lang)
    requires Bisimilar(L1a, L1b)
    requires Bisimilar(L2a, L2b)
    ensures Bisimilar(Comp(L1a, L2a), Comp(L1b, L2b))
  {
    forall k: nat
      ensures Bisimilar#[k](Comp(L1a, L2a), Comp(L1b, L2b))
    {
      if k != 0 {
        var k' :| k' + 1 == k;
        CompCongruenceHelper(k', L1a, L1b, L2a, L2b);
      }
    }
  }

  lemma CompCongruenceHelper<A(!new)>(k: nat, L1a: Lang, L1b: Lang, L2a: Lang, L2b: Lang)
    requires forall n : nat :: n <= k + 1 ==> Bisimilar#[n](L1a, L1b)
    requires forall n : nat :: n <= k + 1 ==> Bisimilar#[n](L2a, L2b)
    ensures Bisimilar#[k+1](Comp(L1a, L2a), Comp(L1b, L2b))
  {
    var lhs := Comp(L1a, L2a);
    var rhs := Comp(L1b, L2b);

    assert Bisimilar#[1](L1a, L1b);
    assert Bisimilar#[1](L2a, L2b);
    assert lhs.eps == rhs.eps;

    forall a 
      ensures (Bisimilar#[k](lhs.delta(a), rhs.delta(a))) 
    {
      var x1 := Comp(L1a.delta(a), L2a);
      var x2 := Comp(L1b.delta(a), L2b);
      assert Bisimilar#[k](x1, x2) by {
        if k != 0 {
          BisimilarCuttingPrefixesPointwise(k, a, L1a, L1b);
          var k' :| k == k' + 1;
          CompCongruenceHelper(k', L1a.delta(a), L1b.delta(a), L2a, L2b);
        }
      }
      var y1 := Comp(if L1a.eps then One() else Zero(), L2a.delta(a));
      var y2 := Comp(if L1b.eps then One() else Zero(), L2b.delta(a));
      assert Bisimilar#[k](y1, y2) by {
        assert L1a.eps == L1b.eps;
        if k != 0 {
          if L1a.eps {
            BisimilarityIsReflexive<A>(One());
            BisimilarCuttingPrefixesPointwise(k, a, L2a, L2b);
            var k' :| k == k' + 1;
            CompCongruenceHelper(k', One<A>(), One<A>(), L2a.delta(a), L2b.delta(a));
          } else {
            BisimilarityIsReflexive<A>(Zero());
            BisimilarCuttingPrefixesPointwise(k, a, L2a, L2b);
            var k' :| k == k' + 1;
            CompCongruenceHelper(k', Zero<A>(), Zero<A>(), L2a.delta(a), L2b.delta(a));
          }
        }
      }
      PlusCongruenceAlternative(k, x1, x2, y1, y2);
    }
  }

  /* Congruence of Star */

  lemma StarCongruence<A(!new)>(L1: Lang, L2: Lang)
    requires Bisimilar(L1, L2)
    ensures Bisimilar(Star(L1), Star(L2))
  {
    forall k: nat
      ensures Bisimilar#[k](Star(L1), Star(L2))
    {
      if k != 0 {
        var k' :| k' + 1 == k;
        StarCongruenceHelper(k', L1, L2);
      }
    }
  }

  lemma StarCongruenceHelper<A(!new)>(k: nat, L1: Lang, L2: Lang)
    requires forall n: nat :: n <= k + 1 ==> Bisimilar#[n](L1, L2)
    ensures Bisimilar#[k+1](Star(L1), Star(L2))
  {
    forall a 
      ensures Bisimilar#[k](Star(L1).delta(a), Star(L2).delta(a)) 
    {
      if k != 0 {
        BisimilarCuttingPrefixesPointwise(k, a, L1, L2);
        var k' :| k == k' + 1;
        forall n: nat
          ensures n <= k' + 1 ==> Bisimilar#[n](Star(L1), Star(L2))
        {
          if 0 < n <= k' + 1 {
            var n' :| n == n' + 1;
            StarCongruenceHelper(n', L1, L2);
          }
        }
        CompCongruenceHelper(k', L1.delta(a), L2.delta(a), Star(L1), Star(L2));
      }
    }
  }

}
