----------------------- MODULE ImageCacheThree -----------------------
EXTENDS FiniteSets, Integers, Sequences
CONSTANT N
VARIABLES image_states, image_queue, keys_used, keys, keys_batch
-----------------------------------------------------------------------------

Image == 1..N
ImageState == {"None", "PendingKey", "HasKey", "Loaded"}


TypeOk == /\ image_states \in [Image -> ImageState]
          /\ image_queue \in Seq(Image)
          /\ keys_used \in Int
          /\ keys \in Seq({"Generated"})
          /\ keys_batch \in BOOLEAN
-----------------------------------------------------------------------------

Init == /\ image_states = [i \in Image |-> "None"]
        /\ image_queue = <<>>
        /\ keys_used = 0
        /\ keys = <<>>
        /\ keys_batch = FALSE
        
StartLoad(i) == /\ image_states[i] = "None"
                /\ image_states' = [image_states EXCEPT ![i] = "PendingKey"]
                /\ image_queue' = Append(image_queue, i)
                /\ UNCHANGED<<keys_used, keys, keys_batch>>
 
GenerateKeys == LET 
                    keys_requested == Cardinality({i \in Image: image_states[i] = "PendingKey"})
                    keys_needed == keys_requested - Len(keys)
                    batch == [i \in 1..keys_needed |-> "Generated"]
                IN
                /\ keys' = IF keys_needed > 0 THEN keys \o batch ELSE keys
                /\ keys_batch' = TRUE
                /\ UNCHANGED<<image_states, image_queue, keys_used>>

SetKey(i) == /\ Len(keys) > 0
             /\ keys_batch = TRUE
             /\ keys' = Tail(keys)
             /\ Head(image_queue) = i
             /\ image_states[i] = "PendingKey" 
             /\ image_states' = [image_states EXCEPT ![i] = "HasKey"]
             /\ keys_used' = keys_used + 1
             /\ UNCHANGED<<image_queue, keys_batch>>

FinishLoad(i) == /\ image_states[i] = "HasKey"
                 /\ Head(image_queue) = i
                 /\ image_states' = [image_states EXCEPT ![i] = "Loaded"]
                 /\ UNCHANGED<<image_queue, keys_used, keys, keys_batch>>
           
DequeImage(i) == /\ Len(image_queue) > 0
                 /\ image_states[i] = "Loaded"
                 /\ Head(image_queue) = i
                 /\ image_queue' = Tail(image_queue)
                 /\ keys_batch' = FALSE
                 /\ UNCHANGED<<image_states, keys_used, keys>>

Done == /\ \A ii \in Image: image_states[ii] = "Loaded"
        /\ UNCHANGED<<image_states, image_queue, keys_used, keys, keys_batch>>

Next == \/ \E i \in Image: \/ StartLoad(i)
                           \/ FinishLoad(i)
                           \/ DequeImage(i)
                           \/ SetKey(i)
        \/ Done
        \/ GenerateKeys
-----------------------------------------------------------------------------
BatchingSpec  ==  Init  /\  [][Next]_<<image_states, image_queue, keys_used, keys, keys_batch>>

StateBar[i \in Image] == CASE image_states[i] \in {"Loaded", "None"} -> image_states[i]
                         []   Len(image_queue) > 0 /\ Head(image_queue) = i -> image_states[i]
                         []   OTHER -> "None"

KeysUsedBar == LET
                front_image_has_key == Len(image_queue) > 0 /\ image_states[Head(image_queue)] = "HasKey"
                images_loaded == Cardinality({i \in Image: image_states[i] \in {"Loaded"}})
               IN
               IF front_image_has_key THEN 1 + images_loaded
               ELSE images_loaded

KeysBar == IF 
             /\ Len(keys) > 0 
             /\ image_states[Head(image_queue)] = "PendingKey"
             /\ keys_batch = TRUE THEN "Generated"
           ELSE "Empty"

Bar == INSTANCE ImageCacheTwo
       WITH image_states <- StateBar,
            keys_used <- KeysUsedBar,
            keys <- KeysBar
            
BarSpec == Bar!NonBlockingSpec
=============================================================================