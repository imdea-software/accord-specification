----------------------------- MODULE ExtraConfiguration -----------------------------
EXTENDS Naturals, Sequences

\* Model checking parameters

\* Command to shards relation
idToShard == [i \in {1, 2, 3} |->
                  CASE i = 1 -> {1}
                    [] i = 2 -> {1}
                    [] i = 3 -> {1, 2}]
		   

\* Conflict relation
ConflictPairs == {
    <<1, 2>>,
    <<1, 3>>
}

\* Initial timestamp values
initTimestampConstantArray == <<[id |-> <<0, 0>>, t |-> 0], [id |-> <<0, 0>>, t |-> 2], [id |-> <<0, 0>> , t |-> 1]>>

=============================================================================
