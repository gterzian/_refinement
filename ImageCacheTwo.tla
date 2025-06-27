--------------------------- MODULE ImageCacheTwo ---------------------------
EXTENDS FiniteSets, Integers, Sequences
CONSTANT N
VARIABLES image_states, keys_used, keys
-----------------------------------------------------------------------------

Image == 1..N
ImageState == {"None", "PendingKey", "HasKey", "Loaded"}


TypeOk == /\ image_states \in [Image -> ImageState]
          /\ keys_used \in Int
          /\ keys \in {"Empty", "Generated"}
-----------------------------------------------------------------------------

Init == /\ image_states = [i \in Image |-> "None"]
        /\ keys_used = 0
        /\ keys = "Empty"
        
StartLoad(i) == /\ image_states[i] = "None"
                /\ \A ii \in Image: image_states[ii] # "PendingKey"
                /\ image_states' = [image_states EXCEPT ![i] = "PendingKey"]
                /\ UNCHANGED<<keys_used, keys>>

GenerateKey == /\ \E i \in Image: image_states[i] = "PendingKey"
               /\ keys' = "Generated"
               /\ keys = "Empty"
               /\ UNCHANGED<<image_states, keys_used>>

SetKey(i) == /\ keys = "Generated"
             /\ keys' = "Empty"
             /\ keys_used' = keys_used + 1
             /\ image_states[i] = "PendingKey"
             /\ image_states' = [image_states EXCEPT ![i] = "HasKey"]
                  
FinishLoad(i) == /\ image_states[i] = "HasKey"
                 /\ image_states' = [image_states EXCEPT ![i] = "Loaded"]
                 /\ UNCHANGED<<keys_used, keys>>

Done == /\ \A ii \in Image: image_states[ii] = "Loaded"
        /\ UNCHANGED<<image_states, keys_used, keys>>

Next == \/ \E i \in Image: \/ StartLoad(i)
                           \/ SetKey(i)
                           \/ FinishLoad(i)
        \/ Done
        \/ GenerateKey
-----------------------------------------------------------------------------
StillBlockingSpec  ==  Init  /\  [][Next]_<<image_states, keys_used, keys>>

StateBar[i \in Image] == IF image_states[i] \in {"PendingKey", "HasKey"}
                         THEN "Loaded" 
                         ELSE image_states[i]

KeysBar == Cardinality({i \in Image: image_states[i] \in {"PendingKey", "HasKey", "Loaded"}})

Bar == INSTANCE ImageCacheOne
       WITH image_states <- StateBar,
            keys_used <- KeysBar
       
BarSpec == Bar!BlockingSpec

THEOREM StillBlockingSpec => BarSpec
=============================================================================