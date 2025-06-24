------------------------- MODULE ImageCacheOne -------------------------
EXTENDS FiniteSets, Integers, Sequences
CONSTANT N
VARIABLES image_states, keys_used
-----------------------------------------------------------------------------
Image == 1..N
ImageState == {"None", "Loaded"}

TypeOk == /\ image_states \in [Image -> ImageState]
          /\ keys_used \in Int
-----------------------------------------------------------------------------

Init == /\ image_states = [i \in Image |-> "None"]
        /\ keys_used = 0
        
LoadImage(i) == /\ image_states[i] = "None"
                /\ keys_used' = keys_used + 1
                /\ image_states' = [image_states EXCEPT ![i] = "Loaded"]

Done == /\ \A ii \in Image: image_states[ii] = "Loaded"
        /\ UNCHANGED<<image_states, keys_used>>

Next == \/ \E i \in Image: \/ LoadImage(i)
        \/ Done
-----------------------------------------------------------------------------
BlockingSpec  ==  Init  /\  [][Next]_<<image_states, keys_used>>
=============================================================================