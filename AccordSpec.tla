---- MODULE AccordSpec ----
EXTENDS TLC, Naturals, Sequences, FiniteSets, ExtraConfiguration


(*

A TLA+ specification of the Accord protocol for transactions in Apache Cassandra

Author: Alexandre SIRET

*)




(***************************************************************************)
(* Constants : these are model checking parameters                         *)
(***************************************************************************)

CONSTANTS
    Shards,     \* The set of shards 
    Proc,       \* The set of processes used in every shard, all shards use same numbered processes
    Id,         \* The set of command IDs
    F,         
    E,
    Bottom,     \* The bottom value for the command payload
    NoProc,      \* A special value representing no process
    Nop,           \* special Nop payload
    NumberOfRecoveryAttempts \* constant used to cap the amount of recovery attempts, this cap is per process command pair.
    \* The following constants are also imported from the ExtraConfiguration module. Look at the file for more details.
    \* idToShard[id] = the set of shards for the id transaction
    \* ConflictPairs is used to define the conflict relation between transactions
    \* initTimestampConstant gives an initial timestamp value for each transaction

N == Cardinality(Proc)
Nshards == Cardinality(Shards)

Max(a, b) == IF a > b THEN a ELSE b
ASSUME N >= Max(2*E+F-1, 2*F+1)

\* Phase constants
InitialPhase        == 1
PreAcceptedPhase    == 2
AcceptedPhase       == 3
FastAcceptedPhase   == 4
CommittedPhase      == 5
StablePhase         == 6

\* Message types
TypeSubmit          == 0
TypePreAccept       == 1
TypePreAcceptOK     == 2
TypeAccept          == 3
TypeAcceptOK        == 4
TypeFastAccept      == 5
TypeFastAcceptOK    == 6
TypeCommit          == 7
TypeCommitOK        == 8
TypeStable          == 9
TypeRecover         == 10
TypeRecoverOK       == 11
TypeRead            == 12
TypeReadOk          == 13
TypeApply           == 14

\* Constants for Fast, Slow or Medium Path
Fast    == 0
Slow    == 1
Medium  == 2

(***************************************************************************)
(* Message constructors                                                    *)
(***************************************************************************)

Message(type, shardfrom, from, shardto, to, body) ==
    [type |-> type, shardfrom |-> shardfrom, from |-> from, to |-> to, shardto |-> shardto, body |-> body]

SubmitMsg(sp, p, sq, q, id) ==
    Message(TypeSubmit, sp, p, sq, q, [id |-> id])

PreAcceptMsg(sp, p, sq, q, id, tx, D0) ==
    Message(TypePreAccept, sp, p, sq, q, [id |-> id, tx |-> tx, D0 |-> D0])

PreAcceptOKMsg(sp, p, sq, q, id, tq, Dq) ==
    Message(TypePreAcceptOK, sp, p, sq, q, [id |-> id, tq |-> tq, Dq |-> Dq])

AcceptMsg(sp, p, sq, q, b, id, t, D, tx) ==
    Message(TypeAccept, sp, p, sq, q, [id |-> id, b |-> b, t |-> t, D |-> D, tx |-> tx])

AcceptOKMsg(sp, p, sq, q, b, id, Dq) ==
    Message(TypeAcceptOK, sp, p, sq, q, [id |-> id, b |-> b, Dq |-> Dq])

FastAcceptMsg(sp, p, sq, q, id, D) ==
    Message(TypeFastAccept, sp, p, sq, q, [id |-> id, D |-> D])

FastAcceptOKMsg(sp, p, sq, q, id) ==
    Message(TypeFastAcceptOK, sp, p, sq, q, [id |-> id])

CommitMsg(sp, p, sq, q, b, id, t, D, DPlus, pathSpeed, tx) ==
    Message(TypeCommit, sp, p, sq, q, [id |-> id, b |-> b, t |-> t, D |-> D, DPlus |-> DPlus, pathSpeed |-> pathSpeed, tx |-> tx])

CommitOKMsg(sp, p, sq, q, b, id) ==
    Message(TypeCommitOK, sp, p, sq, q, [id |-> id, b |-> b])

StableMsg(sp, p, sq, q, b, id) ==
    Message(TypeStable, sp, p, sq, q, [id |-> id, b |-> b])

RecoverMsg(sp, p, sq, q, b, id, tx) ==
    Message(TypeRecover, sp, p, sq, q, [id |-> id, b |-> b, tx |-> tx])

RecoverOkMsg(sp, p, sq, q, b, id, abalq, txq, tq, depq, DPlus, phaseq, rejectq, Wq, WPq) ==
    Message(TypeRecoverOK, sp, p, sq, q, [id |-> id, b |-> b, abalq |-> abalq, txq |-> txq, tq |-> tq, depq |-> depq, DPlus |-> DPlus, phaseq |-> phaseq, rejectq |-> rejectq, Wq |-> Wq, WPq |-> WPq])

ReadMsg(sp, p, sq, q, id) ==
    Message(TypeRead, sp, p, sq, q, [id |-> id])

ReadOkMsg(sp, p, sq, q, id) ==
    Message(TypeReadOk, sp, p, sq, q, [id |-> id])

ApplyMsg(sp, p, sq, q, id) ==
    Message(TypeApply, sp, p, sq, q, [id |-> id])


(***************************************************************************)
(* Variables                                                               *)
(***************************************************************************)

VARIABLES
    \* The following arrays are index by s and p because every individual process is indexed by a shard and process pair.
    bal,           \* bal[s][p][id] = current ballot known by process p in shard s for transaction id
    phase,         \* phase[s][p][id] \in { InitialPhase, PreAcceptedPhase, AcceptedPhase, CommittedPhase, StablePhase }
    txn,           \* txn[s][p][id] = command payload at (s, p)
    dep,           \* dep[s][p][id] = dependency set
    depPlus,       \* depPlus[s][p][id] dep+ set used in execution 
    ts,            \* ts[s][p][id] = timestamp at (s, p), timestamp is a couple of (t, id) ts.t is the timestamp value, ts.id is it's id.
    abal,          \* abal[s][p][id] = the last ballot where (s, p) accepted a slow path value
    msgs,          \* set of network messages
    submitted,     \* set of submitted command ids
    initCoord,     \* the initial coordinator.
    initCoords,    \* initCoords[id][s] = the initial partition coordinator of id in shard s
    initTimestamp, \* id's initial timestamp defined on submit using initTimestampConstant
    recovered,     \* recovered[s][p][id] = counter of times recovery is invoked
    
    \* the following variables are used in recovery to : 
    \* persist local state to the post waiting operation and
    \* keep track of when we are allowed to trigger the post waiting operation
    Wvar,           
    TXvar,
    Dvar,
    Qvar,
    postWaitingFlag,
    recoveryAttemptBal,

    executed,           \* executed[s][p] = the set of executed transactions by (s, p)
    executeWaitingFlag, \* flag to know when a process has already started executing id.
    relation           \* this is the < relation over transactions to check acyclicity


vars == << bal, phase, txn, dep, depPlus, ts, abal, msgs, submitted, initTimestamp, initCoords, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, executed, executeWaitingFlag, relation >>

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init == 
    /\ bal = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> 0]]]
    /\ phase = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> InitialPhase]]]
    /\ txn = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> Bottom]]]
    /\ dep = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> {}]]]
    /\ depPlus = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> {}]]]
    /\ ts = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> [t |-> 0, id |-> <<0, NoProc>>]]] ]
    /\ abal = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> 0]]]
    /\ msgs = {}
    /\ submitted = {}
    /\ initCoord = [id \in Id |-> [shard |-> 0, proc |-> NoProc]]
    /\ initCoords = [id \in Id |-> [shard \in idToShard[id] |-> [shard |-> shard, proc |-> NoProc]]]
    /\ recovered = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> 0]]]
    /\ Wvar = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> {}]]]
    /\ TXvar = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> Bottom]]]
    /\ Dvar = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> {}]]]
    /\ postWaitingFlag = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> FALSE]]]
    /\ recoveryAttemptBal = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> 0]]]
    /\ initTimestamp = initTimestampConstantArray
    /\ Qvar = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> {}]]]
    /\ executed = [s \in Shards |-> [p \in Proc |-> {} ]]
    /\ executeWaitingFlag =  [s \in Shards |-> [p \in Proc |-> [id \in Id |-> FALSE]]]
    /\ relation = [id1 \in Id |-> [id2 \in Id |-> FALSE]]


(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)

\* Relation on timestamps 
LessThanTs(ts1, ts2) ==
    IF ts1.t < ts2.t THEN TRUE
    ELSE IF ts1.t > ts2.t THEN FALSE
    ELSE IF ts1.id[2] = ts2.id[2] THEN ts1.id[1] < ts2.id[1]
    ELSE ts1.id[2] < ts2.id[2]

LessOrEqualTs(ts1, ts2) ==
    LessThanTs(ts1, ts2) \/ ts1 = ts2

MaxTs(ts1, ts2) ==
    IF LessThanTs(ts1, ts2) THEN ts2 ELSE ts1

MaxTsInSet(S) ==
    CHOOSE ts1 \in S : \A ts2 \in S :
                            ts2 # ts1 => LessOrEqualTs(ts2, ts1)

\* ConflictPairs is a model constant defined in ExtraConfiguration
Conflicts(id1, id2) ==
    <<id1, id2>> \in ConflictPairs \/ <<id2, id1>> \in ConflictPairs

IsQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - F
IsFastQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - E

\* Checks that a set of messages is quorum sized within each shard of command id.
IsQuorum(set, id) ==
    \A shard \in idToShard[id] :
        LET quorum == { m \in set : m.shardfrom = shard }
        IN 
        /\ IsQuorumSized(quorum)

\* Checks that a set of messages is fast quorum sized within each shard of command id.
IsFastQuorum(set, id) ==
    \A shard \in idToShard[id] :
        LET quorum == { m \in set : m.shardfrom = shard }
        IN IsFastQuorumSized(quorum)

\* This finds all commands that a process knows of, (checks in payload dependencies ballot and initial coordinator)
SeenIds(s, p) ==
    { id \in Id : 
        \/ txn[s][p][id] # Bottom
        \/ \E id2 \in Id : id \in dep[s][p][id2] \/ id \in depPlus[s][p][id2]
        \/ bal[s][p][id] # 0 
        \/ initCoord[id] = [shard |-> s, proc |-> p]
    }

\* Set computation of all commands that have a non initial payload.
NonBottomPayloadIds(s, p) ==
    { id \in Id : txn[s][p][id] # Bottom }

initCoordInQuorum(id, Q) ==
    \E shard \in idToShard[id] :
        initCoords[id][shard] \in Q

InitPartitionCoordsSubsetQ(id, quorumOfMessages) ==
    \A shard \in idToShard[id] :
        \E m \in quorumOfMessages : m.shardfrom = shard /\ m.from = initCoords[id][shard].proc

(***************************************************************************)
(* State-changing Actions                                                  *)
(***************************************************************************)

\* These operators are the insides of all the 'when received' a single message operations, this split allows me to handle self addressed
\* messages by using the corresponding Apply and computation operations.
\* For example, after we submit a command, we :
\*        - send PreAccept messages to everyone except ourselves
\*        - apply the PreAccept operation on ourselves using ApplyPreAccept()
\*        - Compute the t and D values (see pseudocode) with PreAcceptComputations()
\*        - send PreAcceptOk(id, t, D) to ourselves.

PreAcceptComputations(s, p, sq, q, id, initTs) ==
    LET setOfConflictingTs == { IF ts[s][p][id2].id # <<0, NoProc>> THEN ts[s][p][id2] ELSE initTimestamp[id2] 
                                        : id2 \in { id2 \in NonBottomPayloadIds(s, p) : Conflicts(id, id2)} }
        D == { id2 \in NonBottomPayloadIds(s, p) : (Conflicts(id, id2) /\ LessThanTs(initTimestamp[id2], initTs)) }
    IN
    LET tval == IF setOfConflictingTs = {} THEN 0 ELSE MaxTsInSet(setOfConflictingTs).t + 1
    IN
    LET finalTs == MaxTs(initTs, [t |-> tval, id |-> <<s, p>>])
    IN
    [finalTs |-> finalTs, D |-> D] \* this is the record output by this operation

ApplyPreAccept(sp, p, id, tx, finalTs, D0) ==
    /\  bal[sp][p][id] = 0
    /\  phase[sp][p][id] = InitialPhase
    /\  txn'   = [txn   EXCEPT ![sp][p][id] = tx]
    /\  phase' = [phase EXCEPT ![sp][p][id] = PreAcceptedPhase]
    /\  ts'    = [ts    EXCEPT ![sp][p][id] = finalTs]
    /\  dep'   = [dep   EXCEPT ![sp][p][id] = D0]

AcceptComputations(s, p, id, t) ==
    LET Dq == { id2 \in NonBottomPayloadIds(s, p) : (Conflicts(id, id2) /\ LessThanTs(initTimestamp[id2], t)) }
    IN
    [Dq |-> Dq] 

ApplyAccept(sp, p, b, id, t, D, tx) ==
    /\  bal[sp][p][id] <= b
    /\  abal[sp][p][id] = b => phase[sp][p][id] \notin { CommittedPhase, StablePhase }
    /\  (b = 0 => phase[sp][p][id] = PreAcceptedPhase)
    /\  IF b > 0 THEN txn'  = [txn  EXCEPT ![sp][p][id] = tx] ELSE UNCHANGED txn
    /\  bal'   = [bal   EXCEPT ![sp][p][id] = b]
    /\  abal'  = [abal  EXCEPT ![sp][p][id] = b]
    /\  ts'    = [ts    EXCEPT ![sp][p][id] = t]
    /\  dep'   = [dep   EXCEPT ![sp][p][id] = D]
    /\  phase' = [phase EXCEPT ![sp][p][id] = AcceptedPhase]

\* no local computations when receiving a FastAccept message

ApplyFastAccept(sp, p, id, D) ==
    /\  bal[sp][p][id] = 0
    /\  phase[sp][p][id] = PreAcceptedPhase
    /\  ts'    = [ts    EXCEPT ![sp][p][id] = initTimestamp[id]]
    /\  dep'   = [dep   EXCEPT ![sp][p][id] = D]
    /\  phase' = [phase EXCEPT ![sp][p][id] = FastAcceptedPhase]

\* no local computations when receiving a commit message

ApplyCommit(sp, p, b, id, t, D, DPlus, tx, stable) ==
    /\  bal[sp][p][id] = b
    /\  b = 0 => phase[sp][p][id] \in { PreAcceptedPhase, AcceptedPhase, FastAcceptedPhase }
    /\  abal[sp][p][id] = b => phase[sp][p][id] # StablePhase
    /\  IF b > 0 THEN txn'  = [txn  EXCEPT ![sp][p][id] = tx] ELSE UNCHANGED txn
    /\  abal'       = [abal   EXCEPT ![sp][p][id] = b]
    /\  ts'         = [ts     EXCEPT ![sp][p][id] = t]
    /\  dep'        = [dep    EXCEPT ![sp][p][id] = D]
    /\  depPlus'    = [depPlus    EXCEPT ![sp][p][id] = DPlus]
    /\  IF stable THEN phase' = [phase  EXCEPT ![sp][p][id] = StablePhase] ELSE phase' = [phase  EXCEPT ![sp][p][id] = CommittedPhase]

\* no local computations when receiving a stable message

ApplyStable(sp, p, b, id) ==
    /\  abal[sp][p][id] = bal[sp][p][id]
    /\  bal[sp][p][id] = b
    /\  phase[sp][p][id] = CommittedPhase
    /\  phase' = [phase EXCEPT ![sp][p][id] = StablePhase]

RecoverComputations(s, p, id) ==
    LET D == IF phase[s][p][id] \notin { InitialPhase, PreAcceptedPhase } THEN dep[s][p][id]
                ELSE dep[s][p][id] \cup { id2 \in NonBottomPayloadIds(s, p) : (Conflicts(id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
    IN
    LET S == { id2 \in Id : (id2 # id /\ Conflicts(id, id2) /\ txn[s][p][id2] # Nop /\ id \notin dep[s][p][id2]
             /\(   (phase[s][p][id2] \in { CommittedPhase, StablePhase } /\ LessThanTs(initTimestamp[id], ts[s][p][id2]))  
                \/ (   phase[s][p][id2] = AcceptedPhase   /\   LessThanTs( initTimestamp[id] , initTimestamp[id2])) 
                )                    ) 
             }
        W == { <<id3, abal[s][p][id3]>> : 
                    id3 \in { id2 \in Id :
                                (id2 # id /\ Conflicts(id, id2) /\ txn[s][p][id2] # Nop 
                                /\ ((phase[s][p][id2] = AcceptedPhase /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) /\ LessThanTs(initTimestamp[id], ts[s][p][id2]))
                                      \/ (phase[s][p][id2] \in { InitialPhase, PreAcceptedPhase, FastAcceptedPhase } /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) /\ txn[s][p][id2] # Bottom )
                                   )
                                )
                            }
             }
        WP == { id2 \in Id : id2 # id /\ Conflicts(id, id2) /\ phase[s][p][id2] \in { PreAcceptedPhase, FastAcceptedPhase } 
                                                 /\ LessThanTs(initTimestamp[id], initTimestamp[id2]) /\ id \notin dep[s][p][id2] 
              }
    IN
    [D |-> D, S |-> S, W |-> W, WP |-> WP]

ApplyRecover(sp, p, b, id, tx) ==
        /\  bal[sp][p][id] < b
        /\  bal'  = [bal  EXCEPT ![sp][p][id] = b]
        /\  IF phase[sp][p][id] = InitialPhase THEN  txn'  = [txn  EXCEPT ![sp][p][id] = tx] ELSE UNCHANGED txn

(***************************************************************************)
(* Message handling Actions                                                *)
(***************************************************************************)

(* Submit (lines 1-5) *)

Submit(s, p, id) ==
    /\  id \notin submitted
    /\  s \in idToShard[id] 
    \* all initial coordinators have the same number, in different shards. This is just an arbitrary choice.
    /\  LET initCoordsVal == [shard \in idToShard[id] |-> [shard |-> shard, proc |-> p]]
        IN
        /\  initTimestamp' = [initTimestamp EXCEPT ![id] = [id |-> <<s, p>>, t |-> initTimestamp[id].t]]
        /\  submitted' = submitted \cup {id}
        /\  initCoords' = [initCoords EXCEPT ![id] = initCoordsVal]
        /\  initCoord' = [initCoord EXCEPT ![id] = [shard |-> s, proc |-> p]]
        /\  msgs' = msgs \cup { SubmitMsg(s, p, shard, initCoordsVal[shard].proc, id) : shard \in idToShard[id] }
    /\  UNCHANGED <<bal, abal, txn, phase, ts, dep, depPlus, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, executed, executeWaitingFlag, relation>> 

(* Submit (lines 6-7) *)

HandleSubmit(m) ==
    /\  m.type = TypeSubmit
    /\  LET s  == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            id == m.body.id
        IN 
        /\  LET computations == PreAcceptComputations(s, p, s, p, id, initTimestamp[id])
                tx == id \* we use the id as command payload since it does not matter
            IN
            /\  ApplyPreAccept(s, p, id, tx, computations.finalTs, computations.D) \* slightly confusing here but computations.D is D0 here since this is the self addressed message.
            /\  msgs' = (msgs \ {m}) \cup { PreAcceptMsg(s, p, s, to, id, tx, computations.D) : to \in Proc \ { p } } 
                                     \cup { PreAcceptOKMsg(s, p, sq, q, id, computations.finalTs, computations.D) }  
    /\  UNCHANGED <<initTimestamp, submitted, initCoords, initCoord, depPlus, bal, abal, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, executed, executeWaitingFlag, relation>> 

(* HandlePreAccept (lines 8-16) *)
                   
HandlePreAccept(m) ==
    /\  m.type = TypePreAccept
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            id == m.body.id
            tx  == m.body.tx
            D0 == m.body.D0
        IN 
        LET computations == PreAcceptComputations(s, p, sq, q, id, initTimestamp[id])
        IN
        /\  ApplyPreAccept(s, p, id, tx, computations.finalTs, D0)
        /\  msgs' = (msgs \ {m}) \cup { PreAcceptOKMsg(s, p, initCoord[id].shard, initCoord[id].proc, id, computations.finalTs, computations.D) } \* this response is sent back to the initial coordinator, not the sender.
    /\  UNCHANGED <<bal, abal, submitted, initCoords, initCoord, depPlus, recovered, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Wvar, Qvar, executed, executeWaitingFlag, relation, initTimestamp>>


(* HandlePreAcceptOk (lines 17-24) *)

HandlePreAcceptOK(s, p, id) ==
    /\  bal[s][p][id] = 0
    /\  phase[s][p][id] = PreAcceptedPhase
    /\  LET  quorumOfMessages ==
            { m \in msgs :
                /\ m.type = TypePreAcceptOK
                /\ m.body.id = id
                /\ m.to = p
                /\ m.shardto = s 
            }
        IN
        /\  IsQuorum(quorumOfMessages, id) 
        /\  InitPartitionCoordsSubsetQ(id, quorumOfMessages)
        /\  LET largestFastQuorum ==
                { m \in quorumOfMessages : m.body.tq = initTimestamp[id] }
            IN
            IF IsFastQuorum(largestFastQuorum, id) THEN
                    LET D == UNION { m.body.Dq : m \in largestFastQuorum }
                    IN
                    /\  ApplyFastAccept(s, p, id, D)              
                    /\  msgs' = (msgs \ largestFastQuorum) \cup { FastAcceptMsg(s, p, shard, initCoords[id][shard].proc, id, D) :  shard \in (idToShard[id]) \ {s} }
                                                           \cup { FastAcceptOKMsg(s, p, s, p, id)}
                    /\  UNCHANGED <<bal, abal, txn>>
            ELSE    
                    LET D == UNION { m.body.Dq : m \in quorumOfMessages }
                        t == MaxTsInSet({ m.body.tq : m \in quorumOfMessages })
                    IN
                    LET computations == AcceptComputations(s, p, id, t)
                    IN 
                    /\  ApplyAccept(s, p, 0, id, t, D, txn[s][p][id])
                    /\  msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s, p, to[1], to[2], 0, id, t, D, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } } 
                                                          \cup { AcceptOKMsg(s, p, s, p, 0, id, computations.Dq) }
    /\  UNCHANGED <<submitted, initCoords, initCoord, recovered, depPlus, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar, executed, executeWaitingFlag, relation>>

                     
(* HandleFastAccept (lines 25-28) *)
                    
HandleFastAccept(m) ==
    /\  m.type = TypeFastAccept
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            id == m.body.id
            D  == m.body.D
        IN 
        /\  ApplyFastAccept(s, p, id, D)
        /\  msgs' = (msgs \ {m}) \cup { FastAcceptOKMsg(s, p, sq, q, id) } \*FastAcceptOKmsg does not have D as a param. In my model, the initial coordinator is one of the shard coordinators always, so the D is found in the dep variable of the initial coordinator, see HandleFastAcceptOK
    /\  UNCHANGED <<bal, abal, txn, submitted, initCoords, depPlus, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar, executed, executeWaitingFlag, relation>>

(* HandleFastAcceptOK (lines 29-31) *)

HandleFastAcceptOK(s, p, id) ==
    /\  phase[s][p][id] \in { PreAcceptedPhase, FastAcceptedPhase }
    /\  bal[s][p][id] = 0
    /\  LET setOfMessages == 
            { m \in msgs :
                /\ m.type = TypeFastAcceptOK
                /\ m.to = p
                /\ m.body.id = id
                /\ m.shardto = s 
            }   
        IN
        /\  \A m \in setOfMessages : m.from = initCoords[id][m.shardfrom].proc
        /\  Cardinality(setOfMessages) = Cardinality(idToShard[id])
        /\  ApplyCommit(s, p, 0, id, initTimestamp[id], dep[s][p][id], {}, txn[s][p][id], TRUE) 
        /\  msgs' = (msgs \ setOfMessages)  \cup { CommitMsg(s, p, to[1], to[2], bal[s][p][id], id, ts[s][p][id], dep[s][p][id], {}, Fast, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                                            \cup { StableMsg(s, p, to[1], to[2], bal[s][p][id], id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
    /\  UNCHANGED <<submitted, bal, initTimestamp, initCoords, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, executed, executeWaitingFlag, relation>>

(* HandleAccept (lines 32-37) *)
                           
HandleAccept(m) ==
    /\  m.type = TypeAccept
    /\  LET s  == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            b  == m.body.b
            id == m.body.id
            t  == m.body.t
            D  == m.body.D
            tx == m.body.tx
        IN
        LET computations == AcceptComputations(s, p, id, t)
        IN
        /\  ApplyAccept(s, p, b, id, t, D, tx)
        /\  msgs' = (msgs \ {m}) \cup { AcceptOKMsg(s, p, sq, q, b, id, computations.Dq) }
    /\  UNCHANGED <<submitted, initCoords, initCoord, depPlus, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar, executed, executeWaitingFlag, relation>>


(* HandleAcceptOk (lines 38-41) *)

HandleAcceptOK(s, p, id) ==
    /\  phase[s][p][id] = AcceptedPhase
    /\  LET quorumOfMessages == 
            { m \in msgs :
                /\ m.type = TypeAcceptOK
                /\ m.to = p
                /\ m.body.b = bal[s][p][id]
                /\ m.body.id = id
                /\ m.shardto = s 
            }   
        IN
        /\  IsQuorum(quorumOfMessages, id)
        /\  LET D == dep[s][p][id] \cup UNION { m.body.Dq : m \in quorumOfMessages }
            IN
            IF  ts[s][p][id] = initTimestamp[id] THEN 
                /\  ApplyCommit(s, p, bal[s][p][id], id, ts[s][p][id], dep[s][p][id], UNION { m.body.Dq : m \in quorumOfMessages }, txn[s][p][id], TRUE)             
                /\  msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(s, p, to[1], to[2], bal[s][p][id], id, ts[s][p][id], dep[s][p][id], UNION { m.body.Dq : m \in quorumOfMessages }, Medium, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                                                      \cup { StableMsg(s, p, to[1], to[2], bal[s][p][id], id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
            ELSE
                /\  ApplyCommit(s, p, bal[s][p][id], id, ts[s][p][id], D, {}, txn[s][p][id], FALSE)
                /\  msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(s, p, to[1], to[2], bal[s][p][id], id, ts[s][p][id], D, {}, Slow, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } } 
                                                      \cup { CommitOKMsg(s, p, s, p, bal[s][p][id], id) } 
    /\  UNCHANGED <<bal, submitted, initCoords, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar, executed, executeWaitingFlag, relation>>


(* HandleCommit (lines 42-47) *)

HandleCommit(m) ==
    /\  m.type = TypeCommit
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            b  == m.body.b
            id == m.body.id
            tx  == m.body.tx
            D  == m.body.D
            DPlus == m.body.DPlus
            pathSpeed == m.body.pathSpeed
            t == m.body.t
        IN
        /\  ApplyCommit(s, p, b, id, t, D, DPlus, tx, FALSE)
        /\  IF pathSpeed = Slow THEN msgs' = (msgs \ {m}) \cup { CommitOKMsg(s, p, sq, q, b, id) } 
            ELSE msgs' = msgs \ {m}
    /\  UNCHANGED <<bal, submitted, initCoords, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, executed, executeWaitingFlag, relation, initTimestamp>>


(* HandleCommitOk (lines 51-53) *)

HandleCommitOK(s, p, id) ==
    /\  phase[s][p][id] = CommittedPhase
    /\  LET quorumOfMessages == 
            { m \in msgs :
                /\ m.type = TypeCommitOK
                /\ m.to = p
                /\ m.body.b = bal[s][p][id]
                /\ m.body.id = id
                /\ m.shardto = s 
            }   
        IN
        /\  IsQuorum(quorumOfMessages, id)
        /\  ApplyStable(s, p, bal[s][p][id], id)
        /\  msgs' = (msgs \ quorumOfMessages) \cup { StableMsg(s, p, to[1], to[2], bal[s][p][id], id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
    /\  UNCHANGED <<bal, txn, dep, depPlus, ts, abal, submitted, initCoords, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar, executed, executeWaitingFlag, relation>>

(* HandleStable (lines 48-50) *)

HandleStable(m) ==
    /\  m.type = TypeStable
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            b  == m.body.b
            id == m.body.id
        IN
        /\  ApplyStable(s, p, b, id)
        /\  msgs' = msgs \ {m}
        /\  UNCHANGED <<bal, submitted, initCoords, initCoord, dep, depPlus, abal, txn, ts, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar, executed, executeWaitingFlag, relation>>


(* StartRecover (lines 54-57) *)

StartRecover(s, p, id) ==
    /\  recovered[s][p][id] < NumberOfRecoveryAttempts
    /\  id \in SeenIds(s, p)
    /\  s \in idToShard[id]
    /\  postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE] 
    /\  recovered' = [recovered EXCEPT ![s][p][id] = recovered[s][p][id] + 1]
    \*  Ballots owned by p are of the form k*N + p. This k computation is just to get the smallest k * N + p larger than the current ballot
    \*  Since 2 processes from different shards can have the same id I compute a new p unique id (N * Nshards of them in total) and use that.
    /\  LET Ntotal == N * Nshards IN
        LET pUnique == ((s-1) * N) + p  IN
        LET k == ((bal[s][p][id] - pUnique + Ntotal) \div Ntotal) IN
        LET b == k * Ntotal + pUnique
        IN
        /\  LET computations == RecoverComputations(s, p, id)
            IN
            LET D == computations.D
                S == computations.S
                W == computations.W
                WP == computations.WP
            IN
            /\  IF phase[s][p][id] = InitialPhase THEN ApplyRecover(s, p, b, id, Nop) ELSE ApplyRecover(s, p, b, id, txn[s][p][id])
            /\  IF S # {}
                THEN IF phase[s][p][id] # InitialPhase THEN msgs' =  msgs \cup { RecoverOkMsg(s, p, s, p, b, id, abal[s][p][id], txn[s][p][id], ts[s][p][id], D, depPlus[s][p][id], phase[s][p][id], TRUE, {}, {}) }  \cup { RecoverMsg(s, p, to[1], to[2], b, id, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ {<<s, p>>} }
                        ELSE                                msgs' =  msgs \cup { RecoverOkMsg(s, p, s, p, b, id, abal[s][p][id], Nop, ts[s][p][id], D, depPlus[s][p][id], phase[s][p][id], TRUE, {}, {}) }            \cup { RecoverMsg(s, p, to[1], to[2], b, id, Nop)           : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ {<<s, p>>} }
                ELSE IF phase[s][p][id] # InitialPhase THEN msgs' =  msgs \cup { RecoverOkMsg(s, p, s, p, b, id, abal[s][p][id], txn[s][p][id], ts[s][p][id], D, depPlus[s][p][id], phase[s][p][id], FALSE, W, WP) } \cup { RecoverMsg(s, p, to[1], to[2], b, id, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ {<<s, p>>} }
                        ELSE                                msgs' =  msgs \cup { RecoverOkMsg(s, p, s, p, b, id, abal[s][p][id], Nop, ts[s][p][id], D, depPlus[s][p][id], phase[s][p][id], FALSE, W, WP) }           \cup { RecoverMsg(s, p, to[1], to[2], b, id, Nop)           : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ {<<s, p>>} }
/\ UNCHANGED <<phase, dep, depPlus, ts, abal, submitted, initCoords, initCoord, Wvar, TXvar, Dvar, initTimestamp, Qvar, executed, executeWaitingFlag, relation,  recoveryAttemptBal>>


(* HandleRecover (lines 58-70) *)

HandleRecover(m) ==
    /\  m.type = TypeRecover
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            b == m.body.b
            id == m.body.id
            tx == m.body.tx
        IN 
        /\  LET computations == RecoverComputations(s, p, id)
            IN
            LET D == computations.D
                S == computations.S
                W == computations.W
                WP == computations.WP
            IN
            /\  ApplyRecover(s, p, b, id, tx)
            /\  IF S # {}
                THEN msgs' = (msgs \ {m}) \cup { RecoverOkMsg(s, p, sq, q, b, id, abal[s][p][id], txn'[s][p][id], ts[s][p][id], D, depPlus[s][p][id], phase[s][p][id], TRUE, {}, {}) } 
                ELSE msgs' = (msgs \ {m}) \cup { RecoverOkMsg(s, p, sq, q, b, id, abal[s][p][id], txn'[s][p][id], ts[s][p][id], D, depPlus[s][p][id], phase[s][p][id], FALSE, W, WP) }
    /\  UNCHANGED <<submitted, initCoords, initCoord, dep, depPlus, abal, ts, phase, recovered, TXvar, Dvar, postWaitingFlag, Wvar, recoveryAttemptBal, initTimestamp, Qvar, executed, executeWaitingFlag, relation>>


(* HandleRecoverOK (lines 71-90 + 100-101) *)

HandleRecoverOK(s, p, id) ==
    /\  LET quorumOfMessages ==
            { m \in msgs :
                /\ m.type = TypeRecoverOK
                /\ m.to = p 
                /\ m.body.id = id 
                /\ m.body.b = bal[s][p][id]
                /\ abal[s][p][id] < m.body.b
                /\ m.shardto = s  
            }
        IN
        /\  IsQuorum(quorumOfMessages, id) 
        /\  LET Q == { [shard |-> m.shardfrom, proc |-> m.from] : m \in quorumOfMessages }
                Abals == { m.body.abalq : m \in quorumOfMessages }
                bmax == CHOOSE val \in Abals : \A val2 \in Abals : val >= val2
                U == { m \in quorumOfMessages : m.body.abalq = bmax }
            IN
            /\  IF (\E n \in U : n.body.phaseq  = StablePhase)
                THEN
                        /\  LET n == CHOOSE n \in U :
                                        n.body.phaseq = StablePhase
                            IN
                            /\  ApplyCommit(s, p, bal[s][p][id], id, n.body.tq, n.body.depq, n.body.DPlus, n.body.txq, TRUE)
                            /\  msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(s, p, to[1], to[2], bal[s][p][id], id, n.body.tq, n.body.depq, n.body.DPlus, Fast, n.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                                                                  \cup { StableMsg(s, p, to[1], to[2], bal[s][p][id], id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                            /\  UNCHANGED <<bal, TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>> 
                ELSE IF (\E n \in U : n.body.phaseq = CommittedPhase)
                THEN
                        LET n == CHOOSE n \in U : n.body.phaseq = CommittedPhase
                        IN
                        /\  ApplyCommit(s, p, bal[s][p][id], id, n.body.tq, n.body.depq, n.body.DPlus, n.body.txq, FALSE)
                        /\  msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(s, p, to[1], to[2], bal[s][p][id], id, n.body.tq, n.body.depq, n.body.DPlus, Slow, n.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } } 
                                                              \cup { CommitOKMsg(s, p, s, p, bal[s][p][id], id) }
                        /\  UNCHANGED <<bal, TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>  
                ELSE IF (\E n \in U : n.body.phaseq \in { AcceptedPhase, FastAcceptedPhase })
                THEN    
                        /\  LET n == CHOOSE n \in U :
                                n.body.phaseq \in { AcceptedPhase, FastAcceptedPhase }
                            IN
                            LET computations == AcceptComputations(s, p, id, n.body.tq)
                            IN  
                            /\  ApplyAccept(s, p, bal[s][p][id], id, n.body.tq, n.body.depq, n.body.txq)
                            /\  msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, n.body.tq, n.body.depq, n.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } } 
                                                                  \cup { AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq) }
                            /\  UNCHANGED <<TXvar, depPlus, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>> 
                ELSE IF (initCoordInQuorum(id, Q))
                THEN 
                        LET computations == AcceptComputations(s, p, id, initTimestamp[id])
                        IN 
                        /\  ApplyAccept(s, p, bal[s][p][id], id, initTimestamp[id], dep[s][p][id], Nop)            
                        /\  msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, initTimestamp[id], dep[s][p][id], Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } } 
                                                              \cup { AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq) } 
                        /\  UNCHANGED <<TXvar, Wvar, depPlus, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
                ELSE IF ( \A shard \in idToShard[id] :
                            LET Rmax == { n \in quorumOfMessages :
                                            /\  n.body.phaseq = PreAcceptedPhase
                                            /\  n.shardfrom = shard
                                            /\  n.body.tq = initTimestamp[id] 
                                        }
                            IN Cardinality(Rmax) >= Cardinality({ n \in quorumOfMessages : n.shardfrom = shard }) - E)
                        THEN
                        LET rejects == { m \in quorumOfMessages : m.body.rejectq = TRUE }
                        IN
                        IF (rejects # {} 
                            \/  (\E shard \in idToShard[id] :
                                    LET shardQuorum == { n \in quorumOfMessages : n.shardfrom = shard }
                                    IN ((Cardinality({ m \in shardQuorum : m.body.phaseq = PreAcceptedPhase /\ m.body.tq = initTimestamp[id] }) = Cardinality(shardQuorum ) - E)
                                        /\ \E id2 \in UNION { m.body.WPq : m \in shardQuorum } : initCoords[id2][shard] \notin Q )
                                )
                           )   
                        THEN 
                            LET computations == AcceptComputations(s, p, id, initTimestamp[id])
                            IN 
                            /\  ApplyAccept(s, p, bal[s][p][id], id, initTimestamp[id], dep[s][p][id], Nop)                    
                            /\  msgs' = (msgs\ quorumOfMessages) \cup { AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, initTimestamp[id], dep[s][p][id], Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } } 
                                                                 \cup { AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq) } 
                            /\  UNCHANGED <<TXvar, Wvar, Dvar, depPlus, recoveryAttemptBal, postWaitingFlag, Qvar>>   
                        ELSE 
                            LET n == CHOOSE n \in quorumOfMessages : n.body.phaseq = PreAcceptedPhase
                                Wall == UNION { (m.body.Wq \cup { <<id1, 0>> : id1 \in { id2 \in m.body.WPq : [shard |-> m.shardfrom, proc |-> m.from] = initCoords[id2][m.shardfrom] } }) : m \in quorumOfMessages }
                            IN
                            LET tx == n.body.txq
                                W == { <<id1, bal1>> \in Wall : \A <<id2, bal2>> \in Wall : id2 = id1 => bal2 <= bal1 }
                                D == UNION { m.body.depq : m \in quorumOfMessages }
                            IN
                            /\  TXvar' = [TXvar EXCEPT  ![s][p][id] = tx]
                            /\  Wvar'  = [Wvar  EXCEPT  ![s][p][id] = W]
                            /\  Dvar'  = [Dvar  EXCEPT  ![s][p][id] = D]
                            /\  Qvar'  = [Qvar  EXCEPT  ![s][p][id] = Q]
                            /\  postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = TRUE]
                            /\  recoveryAttemptBal' = [recoveryAttemptBal EXCEPT ![s][p][id] = bal[s][p][id]]
                            /\  msgs' = msgs \ quorumOfMessages
                            /\  UNCHANGED <<bal, txn, abal, ts, dep, depPlus, phase>>
                ELSE  
                    LET computations == AcceptComputations(s, p, id, initTimestamp[id])
                    IN 
                    /\  ApplyAccept(s, p, bal[s][p][id], id, initTimestamp[id], dep[s][p][id], Nop)
                    /\  msgs' =   (msgs \ quorumOfMessages)  \cup { AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, initTimestamp[id], {}, Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } } 
                                                             \cup { AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq) } 
                    /\  UNCHANGED <<TXvar, Wvar, Dvar, depPlus, recoveryAttemptBal, postWaitingFlag, Qvar>>   
    /\  UNCHANGED <<submitted, initCoords, initCoord, recovered, initTimestamp, executed, executeWaitingFlag, relation>>

                 
(* HandlePostWaiting (lines 91-99) *)
                    
HandlePostWaiting(s, p, id) ==
    /\  recoveryAttemptBal[s][p][id] = bal[s][p][id] \* I'm not getting the ballot of corresponding recovery attempt from messages here so I use this extra variable to check we havn't moved ballot.
    /\  postWaitingFlag[s][p][id] = TRUE
    /\  LET W == Wvar[s][p][id]
            b == bal[s][p][id] 
            tx == TXvar[s][p][id]
            D == Dvar[s][p][id]
            Q == Qvar[s][p][id]
            Case1 ==
                \E w \in W :
                    LET id1 == w[1]
                        bal1 == w[2]
                    IN
                    LET sI == IF s \in idToShard[id1] THEN s ELSE CHOOSE sInter \in Shards : sInter \in idToShard[id1] /\ sInter \in idToShard[id]
                    IN
                    \* If id1 not in the shard s, go find a shard in the intersection. and check that on one of this process. 
                    /\  phase[sI][p][id1] \in { CommittedPhase, StablePhase }
                    /\  abal[sI][p][id1] >= bal1
                    /\  txn[sI][p][id1] # Nop
                    /\  LessThanTs(initTimestamp[id], ts[sI][p][id1])
                    /\  id \notin dep[sI][p][id1]
            Case2 ==
                \A w \in W :
                    LET id1 == w[1]
                        bal1 == w[2]
                    IN 
                    LET sI == IF s \in idToShard[id1] THEN s ELSE CHOOSE sInter \in Shards : sInter \in idToShard[id1] /\ sInter \in idToShard[id]
                    IN
                    /\  phase[sI][p][id1] \in { CommittedPhase, StablePhase }
                    /\  abal[sI][p][id1] >= bal1
                    /\  (txn[sI][p][id1] = Nop \/ LessThanTs(ts[sI][p][id1], initTimestamp[id]) \/ id \in dep[sI][p][id1])
            Case3 ==
                (\E m \in msgs :
                    /\  m.type = TypeRecoverOK
                    /\  m.body.b = b
                    /\  m.body.id = id
                    /\  m.to = p
                    /\  [shard |-> m.shardfrom, proc |-> m.from] \notin Q
                    /\  (m.body.phaseq \in { StablePhase, CommittedPhase, AcceptedPhase, FastAcceptedPhase } \/ [shard |-> m.shardfrom, proc |-> m.from] = initCoords[id][m.shardfrom])
                )
        IN 
        \/  /\  Case1
            /\  LET computations == AcceptComputations(s, p, id, initTimestamp[id])
                IN
                /\  ApplyAccept(s, p, bal[s][p][id], id, initTimestamp[id], {}, Nop) 
                /\  msgs' = msgs \cup { AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, initTimestamp[id], dep[s][p][id], Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                                 \cup { AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq) }
                /\  postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
                /\  UNCHANGED depPlus

        \/  /\  Case2
            /\  LET computations == AcceptComputations(s, p, id, initTimestamp[id])
                IN 
                /\  ApplyAccept(s, p, bal[s][p][id], id, initTimestamp[id], D, tx)
                /\  msgs' = msgs \cup { AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, initTimestamp[id], D, tx) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                                 \cup { AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq) }
                /\  postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
                /\  UNCHANGED depPlus
        \* If I use case 3 here the interpreter doesn't know what m is, which I need in the following. This begs the question why am I
        \* defining the cases seperately in the first place : I need to specify that the state doesn't change when none of the 3 cases are verified. (at the end of this handler)
        \/  (\E m \in msgs :
                    /\  m.type = TypeRecoverOK
                    /\  m.body.b = b
                    /\  m.body.id = id
                    /\  m.to = p
                    /\  [shard |-> m.shardfrom, proc |-> m.from] \notin Q
                    /\  (m.body.phaseq \in { StablePhase, CommittedPhase, AcceptedPhase, FastAcceptedPhase } \/ [shard |-> m.shardfrom, proc |-> m.from] = initCoords[id][m.shardfrom])
                    /\  IF (m.body.phaseq = StablePhase) THEN
                            /\  ApplyCommit(s, p, b, id, m.body.tq, m.body.depq, m.body.DPlus, m.body.txq, TRUE)              
                            /\  msgs' = msgs \cup { CommitMsg(s, p, to[1], to[2], b, id, m.body.tq, m.body.depq, m.body.DPlus, Fast, m.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                                             \cup { StableMsg(s, p, to[1], to[2], b, id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                            /\  postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
                            /\  UNCHANGED bal
                        ELSE IF (m.body.phaseq = CommittedPhase) THEN   
                            /\  ApplyCommit(s, p, b, id, m.body.tq, m.body.depq, m.body.DPlus, m.body.txq, FALSE)
                            /\  msgs' = msgs \cup { CommitMsg(s, p, to[1], to[2], b, id, m.body.tq, m.body.depq, m.body.DPlus, Slow, m.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } } 
                                             \cup { CommitOKMsg(s, p, s, p, b, id) }
                            /\  postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
                            /\  UNCHANGED bal
                        ELSE IF (m.body.phaseq \in { AcceptedPhase, FastAcceptedPhase }) THEN 
                            LET computations == AcceptComputations(s, p, id, m.body.tq)
                            IN 
                            /\  ApplyAccept(s, p, b, id, m.body.tq, m.body.depq, m.body.txq)
                            /\  msgs' = msgs \cup { AcceptMsg(s, p, to[1], to[2], b, id, m.body.tq, m.body.depq, m.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } } 
                                             \cup { AcceptOKMsg(s, p, s, p, b, id, computations.Dq) }
                            /\  postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
                            /\  UNCHANGED depPlus
                        ELSE 
                            LET computations == AcceptComputations(s, p, id, initTimestamp[id])
                            IN 
                            /\  ApplyAccept(s, p, bal[s][p][id], id, initTimestamp[id], dep[s][p][id], Nop)
                            /\  msgs' = msgs \cup { AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, initTimestamp[id], {}, Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } } 
                                             \cup { AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq) } 
                            /\  postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
                            /\  UNCHANGED depPlus
            )

        \* If none of the cases are pass, the model checker still has to be explicitly told that the next state is unchanged.
        \/  /\  ~Case1 /\ ~Case2 /\ ~Case3
            /\  UNCHANGED <<msgs, postWaitingFlag, bal, dep, depPlus, phase, abal, txn, ts>>
                      
    /\  UNCHANGED <<submitted, initCoords, initCoord, recovered, Wvar, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar, executed, executeWaitingFlag, relation>>

(***************************************************************************)
(* Execution                                                               *)
(***************************************************************************) 

(* StartExecute (lines 92-95) *)
StartExecute(s, p, id) ==
    /\  s \in idToShard[id]
    /\  initCoords[id][s].proc = p
    /\  phase[s][p][id] = StablePhase
    /\  executeWaitingFlag[s][p][id] = FALSE
    /\  msgs' = msgs \cup { ReadMsg(s, p, sq, p, id) : sq \in idToShard[id] }
    /\  executeWaitingFlag' = [executeWaitingFlag EXCEPT ![s][p][id] = TRUE]
    /\  UNCHANGED <<bal, phase, txn, dep, depPlus, ts, abal, submitted, initTimestamp, initCoords, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, executed, relation>>
    
(* HandleRead (lines 99-101) *)
HandleRead(m) ==
    /\  m.type = TypeRead
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            id == m.body.id
        IN
        /\  phase[s][p][id] = StablePhase
        /\  \A id2 \in dep[s][p][id] \cup depPlus[s][p][id] : s \in idToShard[id2] => ( phase[s][p][id2] \in { CommittedPhase, StablePhase } /\ (LessThanTs(ts[s][p][id2], ts[s][p][id]) => id2 \in executed[s][p]))
        /\  msgs' = (msgs \ {m}) \cup { ReadOkMsg(s, p, sq, q, id) }
    /\  UNCHANGED <<bal, phase, txn, dep, depPlus, ts, abal, submitted, initTimestamp, initCoords, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, executed, executeWaitingFlag, relation>>

(* When received readOks (lines 96-98) *)
HandleReadOk(s, p, id) ==
    /\ executeWaitingFlag[s][p][id] = TRUE
    /\  LET readOKs ==
            { m \in msgs :
                /\  m.type = TypeReadOk
                /\  m.to = p
                /\  m.body.id = id
                /\  m.shardto = s
            }
        IN
        /\  Cardinality(readOKs) = Cardinality(idToShard[id])
        /\  msgs' = (msgs \ readOKs) \cup { ApplyMsg(s, p, to[1], to[2], id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } }
        /\  relation' =
                [id1 \in Id |->
                    [id2 \in Id |->
                        IF id1 = id /\ id2 \notin submitted /\ txn[s][p][id] # Nop THEN TRUE
                        ELSE relation[id1][id2]
                    ]
                ]
    /\  UNCHANGED <<bal, phase, txn, dep, depPlus, ts, abal, submitted, initTimestamp, initCoords, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, executed, executeWaitingFlag>>
            
(* HandleApply (lines 102-105) *)
HandleApply(m) == 
    /\  m.type = TypeApply
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            id == m.body.id
        IN
        /\  id \notin executed[s][p]
        /\  phase[s][p][id] = StablePhase
        /\  \A id2 \in dep[s][p][id] \cup depPlus[s][p][id] : s \in idToShard[id2] => ( phase[s][p][id2] \in { CommittedPhase, StablePhase } /\ (LessThanTs(ts[s][p][id2], ts[s][p][id]) => id2 \in executed[s][p]))
        /\  msgs' = msgs \ {m}
        /\  executed' = [executed EXCEPT ![s][p] = executed[s][p] \cup {id}]
        /\  relation' =
                [id1 \in Id |->
                    [id2 \in Id |->
                        IF id2 = id /\ Conflicts(id1, id) /\ id1 \in executed[s][p] /\ txn[s][p][id1] # Nop /\ txn[s][p][id2] # Nop
                        THEN TRUE
                        ELSE relation[id1][id2]
                    ]
                ]
    /\  UNCHANGED <<bal, phase, txn, dep, depPlus, ts, abal, submitted, initTimestamp, initCoords, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, executeWaitingFlag>>

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)                 

Agreement ==
  \A id \in Id : \A p, q \in Proc : \A s \in Shards :
    /\  phase[s][p][id] \in { CommittedPhase, StablePhase }
    /\  phase[s][q][id] \in { CommittedPhase, StablePhase }
    =>  /\  txn[s][p][id] = txn[s][q][id]
        /\  ts[s][p][id] = ts[s][q][id]

Ordering ==
  \A id1, id2 \in Id :
        \A p, q \in Proc : \A s \in Shards  :
        /\  phase[s][p][id1] = StablePhase
        /\  phase[s][q][id2] = CommittedPhase
        /\  txn[s][p][id1] # Nop
        /\  txn[s][q][id2] # Nop
        /\  Conflicts(id1, id2)
        /\  LessThanTs(ts[s][q][id2], ts[s][p][id1])
        =>  id2 \in dep[s][p][id1] \cup depPlus[s][p][id1]

Edges ==
    { <<i, j>> \in Id \X Id : relation[i][j] }

RECURSIVE Reach(_,_)

Reach(i, j) ==
    \/  <<i, j>> \in Edges
    \/  \E k \in Id : <<i, k>> \in Edges /\ Reach(k, j)

Acyclicity ==
    \A i \in Id : ~Reach(i, i)


AllCommandsStable ==
    \A id \in Id :
        \A shard \in idToShard[id] :
            \A p \in Proc :
                phase[shard][p][id] = StablePhase

Liveness == <>AllCommandsStable


Next ==
    \/  \E m \in msgs :
        \/  HandleSubmit(m)
        \/  HandlePreAccept(m)
        \/  HandleFastAccept(m) 
        \/  HandleAccept(m)
        \/  HandleCommit(m)
        \/  HandleStable(m)
        
        \/  HandleRecover(m)

        \/  HandleRead(m)
        \/  HandleApply(m)

    \/  \E s \in Shards, p \in Proc, id \in Id :
        \/  Submit(s, p, id)
        \/  HandlePreAcceptOK(s, p, id)
        \/  HandleFastAcceptOK(s, p, id) 
        \/  HandleAcceptOK(s, p, id) 
        \/  HandleCommitOK(s, p, id)
        
        \/  StartRecover(s, p, id)
        \/  HandleRecoverOK(s, p, id)
        \/  HandlePostWaiting(s, p, id) 

        \/  StartExecute(s, p, id)
        \/  HandleReadOk(s, p, id) 


Fairness == WF_vars(Next)

Spec ==
    Init /\ [][Next]_vars /\ Fairness

=========================================================================
