---- MODULE temp ----


PreAcceptComputations(s, p, sq, q, id, initTs) ==
    LET setOfConflictingTs == { ts[s][p][id2] : id2 \in { id2 \in Id : ts[s][p][id2].id # <<0,NoProc>> /\ Conflicts(id, id2)} }
        D == { id2 \in SeenIds(s, p) : (Conflicts(id, id2) /\ LessThanTs(initTimestamp[id2], initTs)) }
    IN
    LET tval == IF setOfConflictingTs = {} THEN 0 ELSE MaxTsInSet(setOfConflictingTs).t + 1
    IN
    LET finalTs == MaxTs(initTs, [t |-> tval, id |-> <<s, p>>])
    IN
    [finalTs |-> finalTs, D |-> D] \* this is the record output by this operation

ApplyPreAccept(p, id, tx) ==
    /\  bal[p][id] = 0
    /\  phase[p][id] = InitialPhase
    /\  LET setOfConflictingTs == { ts[p][id2] : id2 \in { id2 \in Id : Conflicts(id, id2)} }
        IN
        LET tval == IF setOfConflictingTs = {} THEN 0 ELSE MaxTsInSet(setOfConflictingTs).t + 1
        IN
        LET t == MaxTs(initTimestamp[id], [t |-> tval, id |-> p])
            D == { id2 \in Id : (Conflicts(id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
        IN
        /\  ts'    = [ts    EXCEPT ![p][id] = t]
        /\  txn'   = [txn   EXCEPT ![p][id] = tx]
        /\  phase' = [phase EXCEPT ![p][id] = PreAcceptedPhase]



HandlePreAccept(m) ==
    /\  m.type = TypePreAccept
    /\  ApplyPreAccept(p, id, tx, t)
    /\  msgs' = (msgs \ {m}) \cup { PreAcceptOKMsg(p, q, id, t, D) }


Message(type, from, to, body) ==
    [type |-> type, from |-> from, to |-> to, body |-> body]

PreAcceptMsg(p, q, id, tx) ==
    Message(TypePreAccept, p, q, [id |-> id, tx |-> tx])

Next ==
    \/  \E m \in msgs :
        \/  HandlePreAccept(m)
        \/  HandleAccept(m)
        \/  HandleCommit(m)
        \/  HandleStable(m)
        \/  HandleRecover(m)


Agreement ==
  \A id \in Id : \A p, q \in Proc :
    /\  phase[p][id] \in {CommittedPhase, StablePhase}
    /\  phase[q][id] \in {CommittedPhase, StablePhase}
    =>  /\  txn[p][id] = txn[q][id]
        /\  ts[p][id] = ts[q][id]


Ordering ==
  \A id1, id2 \in Id :
        \A p, q \in Proc :
        /\  phase[p][id1] = StablePhase
        /\  phase[q][id2] = CommittedPhase
        /\  txn[p][id1] # Nop
        /\  txn[q][id2] # Nop
        /\  Conflicts(id1, id2)
        /\  LessThanTs(ts[q][id2], ts[p][id1])
        =>  id2 \in dep[p][id1]

============================