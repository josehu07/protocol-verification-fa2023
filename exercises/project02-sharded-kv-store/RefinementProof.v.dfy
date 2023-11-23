include "IMapHelpers.t.dfy"
include "RefinementObligation.t.dfy"

module RefinementProof refines RefinementObligation {
  import opened IMapHelpers
  import opened MessageType

  // We give you a strategy for an abstraction relation, turn it into an
  // abstraction function, and give you a few predicate to use in assembling
  // your invariant. This help is because some strategies for doing this proof
  // will result in a huge mess of invariants and/or serious issues with
  // verification performance, and we don't want you to go through that.

  // The strategy consists at a high level of showing that at each point in
  // time, every key has an "owner" that maps it to the correct value. A key can
  // either be owned by a host, or by a message in the network; if it's in the
  // network, clients can't request it until that message is delivered.

  datatype MapOwner = HostOwner(id: HostId) | MessageOwner(msg: Message)

  // OwnerValue should say that k maps to val specifically due to the owner o.
  ghost predicate OwnerValue(v: Variables, o: MapOwner, k: int, val: int)
    requires v.WF()
  {
    match o {
      case HostOwner(id) =>
        // What does it mean for host id to own a key (and assign it the value
        // val)?
        // DONE: fill in here (solution: 3 lines)
        && v.ValidHost(id)
        && k in v.hosts[id].m
        && val == v.hosts[id].m[k]
      // END EDIT
      case MessageOwner(msg) =>
        // What does it mean for the network to own a key (and assign it the
        // value val)? This is a new concept relative to the atomic demo from
        // chapter06.
        // DONE: fill in here (solution: 3 lines)
        && msg in v.network.inFlightMessages
        && k in msg.chunk
        && val == msg.chunk[k]
           // END EDIT
    }
  }

  // Helper extraction function for one key's owner and value
  ghost function GetKeyOwnerAndValue(v: Variables, k: int) : (MapOwner,int)
    requires v.WF()
  {
    if exists id, val :: OwnerValue(v, HostOwner(id), k, val) then
      var id, val :| OwnerValue(v, HostOwner(id), k, val);
      (HostOwner(id), val)
    else if exists msg, val :: OwnerValue(v, MessageOwner(msg), k, val) then
      var msg, val :| OwnerValue(v, MessageOwner(msg), k, val);
      (MessageOwner(msg), val)
    else
      (HostOwner(0), 0)
  }

  ghost function GetKeyOwner(v: Variables, k: int) : MapOwner
    requires v.WF()
  {
    GetKeyOwnerAndValue(v, k).0
  }

  ghost function GetKeyValue(v: Variables, k: int) : int
    requires v.WF()
  {
    GetKeyOwnerAndValue(v, k).1
  }

  ghost predicate AbstractionRelation(v: Variables, av: AtomicKV.Variables)
  {
    && v.WF()
    && IsFull(av.table)
    // Use OwnerValue to connect v to av
    // DONE: fill in here (solution: 1 line)
    && forall k | IsKey(k) :: av.table[k] == GetKeyValue(v, k)
    // END EDIT
  }

  /* Now we give you a library of some predicates to write your invariant. These
   * are made {:opaque}, which means you have to be intentional about how you use
   * them and prove them. Feel free to use `reveal OwnerHasSomeValue` for
   * example, but do so locally within an `assert P by { ... }` or `forall x ::
   * P(x) ensures { ... }` so that the definition isn't visible for the whole
   * proof - that will lead to timeouts and you'll have a Bad Time. */

  // This is a Dafny subset type - it's an imap that is known to be full
  type Owners = m:imap<int, MapOwner> | (forall k | IsKey(k) :: k in m)
    ghost witness imap k :: HostOwner(0)

  ghost predicate {:opaque} OwnerHasSomeValue(v: Variables, owner: Owners)
    requires v.WF()
  {
    && forall k | IsKey(k) :: exists val :: OwnerValue(v, owner[k], k, val)
  }

  ghost predicate {:opaque} OwnersDistinct(v: Variables, k: int)
    requires v.WF()
  {
    forall o1: MapOwner, o2: MapOwner, val1: int, val2: int ::
      (OwnerValue(v, o1, k, val1) && OwnerValue(v, o2, k, val2)) ==>
        o1 == o2 && val1 == val2
  }

  lemma use_OwnerHasSomeValue(v: Variables, owner: Owners, k: int) returns (val: int)
    requires v.WF()
    requires OwnerHasSomeValue(v, owner)
    ensures OwnerValue(v, owner[k], k, val)
  {
    assert IsKey(k);
    reveal OwnerHasSomeValue();
    val :| OwnerValue(v, owner[k], k, val);
  }

  lemma use_OwnersDistinct(v: Variables, k: int, o1: MapOwner, val1: int, o2: MapOwner, val2: int)
    requires v.WF()
    requires OwnersDistinct(v, k)
    requires OwnerValue(v, o1, k, val1)
    requires OwnerValue(v, o2, k, val2)
    ensures o1 == o2 && val1 == val2
  {
    assert IsKey(k);
    reveal OwnersDistinct();
  }

  // If o owns some value, it is the owner. This is a useful way to use
  // OwnersDistinct without fully revealing it.
  lemma use_OwnerValue(v: Variables, owners: Owners, o: MapOwner, k: int, val: int)
    requires v.WF()
    requires OwnerHasSomeValue(v, owners)
    requires OwnersDistinct(v, k)
    requires OwnerValue(v, o, k, val)
    ensures owners[k] == o
  {
    var val' := use_OwnerHasSomeValue(v, owners, k);
    reveal OwnersDistinct();
  }

  // We give you the abstraction function, which just uses a trick to turn the
  // relation into a function.
  ghost function VariablesAbstraction(v: Variables) : AtomicKV.Variables
  {
    if exists av :: AbstractionRelation(v, av) then
      var av :| AbstractionRelation(v, av); av
    else AtomicKV.Variables(EmptyMap())
  }

  lemma imap_ext_eq(m1: imap<int, int>, m2: imap<int, int>)
    requires IsFull(m1) && IsFull(m2)
    requires forall k: int :: m1[k] == m2[k]
    ensures m1 == m2
  {}

  lemma UniqueAbstraction(v: Variables, av: AtomicKV.Variables, owners: Owners)
    requires AbstractionRelation(v, av)
    requires OwnerHasSomeValue(v, owners)
    ensures VariablesAbstraction(v) == av
  {
    forall k:int
      ensures VariablesAbstraction(v).table[k] == av.table[k]
    {
      var val := use_OwnerHasSomeValue(v, owners, k);
    }
    // NOTE: this had to be factored into a lemma to work
    imap_ext_eq(VariablesAbstraction(v).table, av.table);
  }

  ghost predicate Inv(v: Variables)
  {
    // DONE: fill in here (solution: 3 lines)
    && v.WF()
    && (forall k:int | IsKey(k) :: OwnersDistinct(v, k))
    && (exists owners:Owners :: OwnerHasSomeValue(v, owners))
    // END EDIT
  }

  ////////////////////////////////////////////////////////////////////////////


  lemma RefinementInit(v: Variables)
    //requires Init(v) // inherited from abstract module
    ensures Inv(v)
    ensures AtomicKV.Init(VariablesAbstraction(v))
  {
    // DONE: fill in here (solution: 12 lines)
    var init_owners:Owners := imap k | IsKey(k) :: HostOwner(0);
    // v meets owner distinct
    forall k | IsKey(k)
      ensures OwnersDistinct(v, k)
    {
      reveal OwnersDistinct();
    }
    // v meets owner has value
    assert exists owners:Owners :: OwnerHasSomeValue(v, owners) by
    {
      forall k | IsKey(k)
        ensures exists val :: OwnerValue(v, init_owners[k], k, val)
      {
        var val := v.hosts[0].m[k];
        assert OwnerValue(v, init_owners[k], k, val);
      }
      reveal OwnerHasSomeValue();
      assert OwnerHasSomeValue(v, init_owners);
    }
    // spec init holds
    var av := AtomicKV.Variables(ZeroMap());
    assert AbstractionRelation(v, av) by
    {
      reveal OwnerHasSomeValue();
      assert OwnerHasSomeValue(v, init_owners);
      forall k | IsKey(k)
        ensures OwnerValue(v, init_owners[k], k, av.table[k])
      {}
    }
    assert OwnerHasSomeValue(v, init_owners) by
    {
      reveal OwnerHasSomeValue();
    }
    UniqueAbstraction(v, av, init_owners);
    assert AtomicKV.Init(VariablesAbstraction(v));
    // END EDIT
  }

  // DONE: fill in here (solution: 204 lines)
  // Your proof goes here. We highly, highly recommend stating and proving a
  // refinement lemma for each step; see the chapter06 demo if you need help
  // structuring that.
  lemma ServeGetPreservesAndRefines(id: HostId, v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event)
    requires Inv(v)
    requires v.WF() && v'.WF() && |v.hosts| == |v'.hosts|
    requires v.ValidHost(id) && v'.ValidHost(id)
    requires Host.ServeGet(v.hosts[id], v'.hosts[id], msgOps, event)
    requires OtherHostsUnchanged(v, v', id)
    requires Network.Next(v.network, v'.network, msgOps)
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    assert v' == v;
    var owners:Owners :| OwnerHasSomeValue(v, owners);
    // v' meets owner distinct
    forall k | IsKey(k)
      ensures OwnersDistinct(v', k)
    {}
    // v' meets owner has value
    assert OwnerHasSomeValue(v', owners);
    // spec next holds
    assert event.GetEvent?;
    assert VariablesAbstraction(v) == VariablesAbstraction(v');
    assert exists av :: AbstractionRelation(v, av) by
    {
      var av := AtomicKV.Variables(imap k | IsKey(k) :: GetKeyValue(v, k));
      assert AbstractionRelation(v, av);
    }
    var av :| AbstractionRelation(v, av);
    assert av.table[event.key] == event.value by
    {
      assert av.table[event.key] == GetKeyValue(v, event.key);
      assert GetKeyValue(v, event.key) == event.value by
      {
        reveal OwnersDistinct();
        use_OwnerValue(v, owners, HostOwner(id), event.key, event.value);
        assert OwnerValue(v, HostOwner(id), event.key, event.value);
      }
    }
    UniqueAbstraction(v, av, owners);
    assert AtomicKV.Get(VariablesAbstraction(v), VariablesAbstraction(v'), event.key, event.value);
  }

  lemma ServePutPreservesAndRefines(id: HostId, v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event)
    requires Inv(v)
    requires v.WF() && v'.WF() && |v.hosts| == |v'.hosts|
    requires v.ValidHost(id) && v'.ValidHost(id)
    requires Host.ServePut(v.hosts[id], v'.hosts[id], msgOps, event)
    requires OtherHostsUnchanged(v, v', id)
    requires Network.Next(v.network, v'.network, msgOps)
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    assert v' == v.(hosts := v.hosts[id := v.hosts[id].(m := v.hosts[id].m[event.key := event.value])]);
    var owners:Owners :| OwnerHasSomeValue(v, owners);
    // v' meets owner distinct
    forall k | IsKey(k)
      ensures OwnersDistinct(v', k)
    {
      reveal OwnersDistinct();
      forall o1: MapOwner, o2: MapOwner, val1: int, val2: int |
        (OwnerValue(v', o1, k, val1) && OwnerValue(v', o2, k, val2))
      ensures o1 == o2 && val1 == val2
      {
        if k == event.key {
          var oldval := use_OwnerHasSomeValue(v, owners, k);
          assert OwnerValue(v, HostOwner(id), k, v.hosts[id].m[k]);
          use_OwnerValue(v, owners, HostOwner(id), k, v.hosts[id].m[k]);
          assert owners[k] == HostOwner(id);
          assert v'.network.inFlightMessages == v.network.inFlightMessages;
          forall m, val:int | m in v'.network.inFlightMessages
            ensures !OwnerValue(v', MessageOwner(m), k, val)
          {
            assert !OwnerValue(v, MessageOwner(m), k, val);
          }
          forall h, val:int | v'.ValidHost(h) && h != id
            ensures !OwnerValue(v', HostOwner(h), k, val)
          {
            assert !OwnerValue(v, HostOwner(h), k, val);
          }
          assert OwnerValue(v', HostOwner(id), k, v'.hosts[id].m[k]);
        } else {
          assert OwnerValue(v, o1, k, val1);
          assert OwnerValue(v, o2, k, val2);
        }
        assert o1 == o2;
      }
    }
    // v' meets owner has value
    assert OwnerHasSomeValue(v', owners) by
    {
      reveal OwnerHasSomeValue();
      forall k | IsKey(k)
        ensures exists val :: OwnerValue(v', owners[k], k, val)
      {
        if k == event.key {
          var oldval := use_OwnerHasSomeValue(v, owners, k);
          assert OwnerValue(v, HostOwner(id), k, v.hosts[id].m[k]);
          use_OwnerValue(v, owners, HostOwner(id), k, v.hosts[id].m[k]);
          assert owners[k] == HostOwner(id);
          assert OwnerValue(v', owners[k], k, event.value);
        } else {
          var oldval := use_OwnerHasSomeValue(v, owners, k);
          assert OwnerValue(v', owners[k], k, oldval);
        }
      }
    }
    // spec next holds
    assert event.PutEvent?;
    assert exists av :: AbstractionRelation(v, av) by
    {
      var av := AtomicKV.Variables(imap k | IsKey(k) :: GetKeyValue(v, k));
      assert AbstractionRelation(v, av);
    }
    var av :| AbstractionRelation(v, av);
    UniqueAbstraction(v, av, owners);
    var av' := av.(table := av.table[event.key := event.value]);
    assert av' == VariablesAbstraction(v') by
    {
      forall k | IsKey(k)
        ensures av'.table[k] == GetKeyValue(v', k)
      {
        reveal OwnersDistinct();
        var val := use_OwnerHasSomeValue(v', owners, k);
        assert OwnerValue(v', owners[k], k, val);
        if k == event.key {
          assert av'.table[k] == event.value;
          use_OwnerValue(v', owners, HostOwner(id), k, v'.hosts[id].m[k]);
          assert owners[k] == HostOwner(id);
          assert val == event.value;
          assert av'.table[k] == GetKeyValue(v', k);
        } else {
          assert av'.table[k] == av.table[k];
          assert OwnerValue(v, owners[k], k, val);
          assert av'.table[k] == GetKeyValue(v', k);
        }
      }
      assert AbstractionRelation(v', av');
      UniqueAbstraction(v', av', owners);
    }
    assert AtomicKV.Put(VariablesAbstraction(v), VariablesAbstraction(v'), event.key, event.value);
  }

  lemma SendMigratePreservesAndRefines(id: HostId, v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event)
    requires Inv(v)
    requires v.WF() && v'.WF() && |v.hosts| == |v'.hosts|
    requires v.ValidHost(id) && v'.ValidHost(id)
    requires Host.SendMigrate(v.hosts[id], v'.hosts[id], msgOps, event)
    requires OtherHostsUnchanged(v, v', id)
    requires Network.Next(v.network, v'.network, msgOps)
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    assert msgOps.send.Some?;
    var msg := msgOps.send.value;
    assert v'.hosts == v.hosts[id := v.hosts[id].(m := MapRemove(v.hosts[id].m, msg.chunk.Keys))];
    assert v'.network.inFlightMessages == v.network.inFlightMessages + { msg };
    var owners:Owners :| OwnerHasSomeValue(v, owners);
    var new_owners := imap k | k in owners :: if k in msg.chunk then MessageOwner(msg) else owners[k];
    // v' meets owner distinct
    forall k | IsKey(k)
      ensures OwnersDistinct(v', k)
    {
      reveal OwnersDistinct();
      forall o1: MapOwner, o2: MapOwner, val1: int, val2: int |
        (OwnerValue(v', o1, k, val1) && OwnerValue(v', o2, k, val2))
      ensures o1 == o2 && val1 == val2
      {
        if k in msg.chunk {
          var oldval := use_OwnerHasSomeValue(v, owners, k);
          assert OwnerValue(v, HostOwner(id), k, v.hosts[id].m[k]);
          use_OwnerValue(v, owners, HostOwner(id), k, v.hosts[id].m[k]);
          assert owners[k] == HostOwner(id);
          forall m, val:int | m in v'.network.inFlightMessages && m != msg
            ensures !OwnerValue(v', MessageOwner(m), k, val)
          {
            assert !OwnerValue(v, MessageOwner(m), k, val);
          }
          forall h, val:int | v'.ValidHost(h)
            ensures !OwnerValue(v', HostOwner(h), k, val)
          {
            if h != id {
              assert !OwnerValue(v, HostOwner(h), k, val);
            }
          }
          assert OwnerValue(v', MessageOwner(msg), k, msg.chunk[k]);
        } else {
          assert OwnerValue(v, o1, k, val1);
          assert OwnerValue(v, o2, k, val2);
        }
        assert o1 == o2;
      }
    }
    // v' meets owner has value
    assert OwnerHasSomeValue(v', new_owners) by
    {
      reveal OwnerHasSomeValue();
      forall k | IsKey(k)
        ensures exists val :: OwnerValue(v', new_owners[k], k, val)
      {
        if k in msg.chunk {
          var oldval := use_OwnerHasSomeValue(v, owners, k);
          assert OwnerValue(v, HostOwner(id), k, v.hosts[id].m[k]);
          use_OwnerValue(v, owners, HostOwner(id), k, v.hosts[id].m[k]);
          assert owners[k] == HostOwner(id);
          assert new_owners[k] == MessageOwner(msg);
          assert v.hosts[id].m[k] == msg.chunk[k];
          assert OwnerValue(v', new_owners[k], k, msg.chunk[k]);
        } else {
          var oldval := use_OwnerHasSomeValue(v, owners, k);
          assert OwnerValue(v', owners[k], k, oldval);
          assert owners[k] == new_owners[k];
          assert OwnerValue(v', new_owners[k], k, oldval);
        }
      }
    }
    // spec next holds
    assert event.NoOpEvent?;
    assert exists av :: AbstractionRelation(v, av) by
    {
      var av := AtomicKV.Variables(imap k | IsKey(k) :: GetKeyValue(v, k));
      assert AbstractionRelation(v, av);
    }
    var av :| AbstractionRelation(v, av);
    UniqueAbstraction(v, av, owners);
    assert av == VariablesAbstraction(v') by
    {
      forall k | IsKey(k)
        ensures av.table[k] == GetKeyValue(v', k)
      {
        reveal OwnersDistinct();
        var val := use_OwnerHasSomeValue(v, owners, k);
        assert OwnerValue(v, owners[k], k, val);
        var new_val := use_OwnerHasSomeValue(v', new_owners, k);
        assert OwnerValue(v', new_owners[k], k, new_val);
        if k in msg.chunk {
          use_OwnerValue(v, owners, HostOwner(id), k, v.hosts[id].m[k]);
          assert owners[k] == HostOwner(id);
          assert av.table[k] == v.hosts[id].m[k];
          use_OwnerValue(v', new_owners, MessageOwner(msg), k, msg.chunk[k]);
          assert new_owners[k] == MessageOwner(msg);
          assert new_val == msg.chunk[k];
          assert msg.chunk[k] == v.hosts[id].m[k];
          assert av.table[k] == GetKeyValue(v', k);
        } else {
          assert owners[k] == new_owners[k];
          assert OwnerValue(v, owners[k], k, val);
          assert av.table[k] == GetKeyValue(v', k);
        }
      }
      assert AbstractionRelation(v', av);
      UniqueAbstraction(v', av, new_owners);
    }
    assert AtomicKV.NoOp(VariablesAbstraction(v), VariablesAbstraction(v'));
  }

  lemma RecvMigratePreservesAndRefines(id: HostId, v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event)
    requires Inv(v)
    requires v.WF() && v'.WF() && |v.hosts| == |v'.hosts|
    requires v.ValidHost(id) && v'.ValidHost(id)
    requires Host.RecvMigrate(v.hosts[id], v'.hosts[id], msgOps, event)
    requires OtherHostsUnchanged(v, v', id)
    requires Network.Next(v.network, v'.network, msgOps)
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    assert msgOps.recv.Some?;
    var msg := msgOps.recv.value;
    assert v'.hosts == v.hosts[id := v.hosts[id].(m := IMapUnionPreferLeft(msg.chunk, v.hosts[id].m))];
    assert v'.network.inFlightMessages == v.network.inFlightMessages - { msg };
    var owners:Owners :| OwnerHasSomeValue(v, owners);
    var new_owners := imap k | k in owners :: if k in msg.chunk then HostOwner(id) else owners[k];
    // v' meets owner distinct
    forall k | IsKey(k)
      ensures OwnersDistinct(v', k)
    {
      reveal OwnersDistinct();
      forall o1: MapOwner, o2: MapOwner, val1: int, val2: int |
        (OwnerValue(v', o1, k, val1) && OwnerValue(v', o2, k, val2))
      ensures o1 == o2 && val1 == val2
      {
        if k in msg.chunk {
          var oldval := use_OwnerHasSomeValue(v, owners, k);
          assert OwnerValue(v, MessageOwner(msg), k, msg.chunk[k]);
          use_OwnerValue(v, owners, MessageOwner(msg), k, msg.chunk[k]);
          assert owners[k] == MessageOwner(msg);
          forall m, val:int | m in v'.network.inFlightMessages
            ensures !OwnerValue(v', MessageOwner(m), k, val)
          {
            assert !OwnerValue(v, MessageOwner(m), k, val);
          }
          forall h, val:int | v'.ValidHost(h) && h != id
            ensures !OwnerValue(v', HostOwner(h), k, val)
          {
            assert !OwnerValue(v, HostOwner(h), k, val);
          }
          assert OwnerValue(v', HostOwner(id), k, v'.hosts[id].m[k]);
        } else {
          assert OwnerValue(v, o1, k, val1);
          assert OwnerValue(v, o2, k, val2);
        }
        assert o1 == o2;
      }
    }
    // v' meets owner has value
    assert OwnerHasSomeValue(v', new_owners) by
    {
      reveal OwnerHasSomeValue();
      forall k | IsKey(k)
        ensures exists val :: OwnerValue(v', new_owners[k], k, val)
      {
        if k in msg.chunk {
          var oldval := use_OwnerHasSomeValue(v, owners, k);
          assert OwnerValue(v, MessageOwner(msg), k, msg.chunk[k]);
          use_OwnerValue(v, owners, MessageOwner(msg), k, msg.chunk[k]);
          assert owners[k] == MessageOwner(msg);
          assert new_owners[k] == HostOwner(id);
          assert v'.hosts[id].m[k] == msg.chunk[k];
          assert OwnerValue(v', new_owners[k], k, v'.hosts[id].m[k]);
        } else {
          var oldval := use_OwnerHasSomeValue(v, owners, k);
          assert OwnerValue(v', owners[k], k, oldval);
          assert owners[k] == new_owners[k];
          assert OwnerValue(v', new_owners[k], k, oldval);
        }
      }
    }
    // spec next holds
    assert event.NoOpEvent?;
    assert exists av :: AbstractionRelation(v, av) by
    {
      var av := AtomicKV.Variables(imap k | IsKey(k) :: GetKeyValue(v, k));
      assert AbstractionRelation(v, av);
    }
    var av :| AbstractionRelation(v, av);
    UniqueAbstraction(v, av, owners);
    assert av == VariablesAbstraction(v') by
    {
      forall k | IsKey(k)
        ensures av.table[k] == GetKeyValue(v', k)
      {
        reveal OwnersDistinct();
        var val := use_OwnerHasSomeValue(v, owners, k);
        assert OwnerValue(v, owners[k], k, val);
        var new_val := use_OwnerHasSomeValue(v', new_owners, k);
        assert OwnerValue(v', new_owners[k], k, new_val);
        if k in msg.chunk {
          use_OwnerValue(v, owners, MessageOwner(msg), k, msg.chunk[k]);
          assert owners[k] == MessageOwner(msg);
          assert av.table[k] == msg.chunk[k];
          use_OwnerValue(v', new_owners, HostOwner(id), k, v'.hosts[id].m[k]);
          assert new_owners[k] == HostOwner(id);
          assert new_val == v'.hosts[id].m[k];
          assert msg.chunk[k] == v'.hosts[id].m[k];
          assert av.table[k] == GetKeyValue(v', k);
        } else {
          assert owners[k] == new_owners[k];
          assert OwnerValue(v, owners[k], k, val);
          assert av.table[k] == GetKeyValue(v', k);
        }
      }
      assert AbstractionRelation(v', av);
      UniqueAbstraction(v', av, new_owners);
    }
    assert AtomicKV.NoOp(VariablesAbstraction(v), VariablesAbstraction(v'));
  }
  // END EDIT

  lemma RefinementNext(v: Variables, v': Variables, event: Event)
    // These requires & ensures all come from RefinementObligations; repeating
    // them here as a nearby crib sheet.
    // requires Next(v, v')
    // requires Inv(v)
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    var dsstep: Step :| NextStep(v, v', event, dsstep);
    var msgOps := dsstep.msgOps;
    var id := dsstep.hostId;
    assert Host.Next(v.hosts[id], v'.hosts[id], msgOps, event);
    var step: Host.Step :| Host.NextStep(v.hosts[id], v'.hosts[id], msgOps, event, step);
    // All the solution dos here is match on the step and call the lemma for
    // refinement of that step.
    // DONE: fill in here (solution: 14 lines)
    match step {
      case ServeGetStep => ServeGetPreservesAndRefines(id, v, v', msgOps, event);
      case ServePutStep => ServePutPreservesAndRefines(id, v, v', msgOps, event);
      case SendMigrateStep => SendMigratePreservesAndRefines(id, v, v', msgOps, event);
      case RecvMigrateStep => RecvMigratePreservesAndRefines(id, v, v', msgOps, event);
    }
    // END EDIT
  }
}
