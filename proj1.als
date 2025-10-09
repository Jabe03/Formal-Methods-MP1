
--===============================================
-- CS:5810 Formal Methods in Software Engineering
-- Fall 2023
--
-- Mini Project 1
--
-- Name:  <your name(s) here>
--
--===============================================

enum Status {External, Fresh, Active, Purged}

abstract sig Object {}

sig Message extends Object {
  var status: lone Status
}

sig Mailbox extends Object {
  var messages: set Message  
}

-- Mail application
one sig Mail {
  -- system mailboxes
  inbox: Mailbox,
  drafts: Mailbox,
  trash: Mailbox,
  sent: Mailbox,
  -- user mailboxes
  var uboxes: set Mailbox,

  var op: lone Operator -- added for tracking purposes only
}

-- added for your convenience, to track the operators applied during 
-- a system execution 
enum Operator {CMB, DMB, CM, GM, SM, DM, MM, ET}

-- Since we have only one Mail app, it is convenient to have
-- a global shorthand for its system mailboxes
fun sboxes : set Mailbox { Mail.inbox + Mail.drafts + Mail.trash + Mail.sent }

------------------------------
-- Frame condition predicates
------------------------------

-- You may use these predicates in the definition of the operators

-- the status of the messages in M is unchanged from a state to the next
pred noStatusChange [M: set Message] {
  all m: M | m.status' = m.status
}

-- the set of messages in each mailbox in MB is unchanged from a state to the next
pred noMessageChange [MB: set Mailbox] {
  all mb: MB | mb.messages' = mb.messages
}

-- the set of user-defined mailboxes is unchanged from a state to the next
pred noUserboxChange {
  Mail.uboxes' = Mail.uboxes
}

-------------
-- Operators
-------------

/* NOTE: Leave the constraint on Mail.op' in the operators.
   It is there to track the applied operators in each trace  
*/


-- createMessage 
pred createMessage [m: Message] {
  
  --pre conditions

  --post conditions

  --frame conditions


  Mail.op' = CM
}

-- getMessage 
pred getMessage [m: Message] {
  --pre conditions

  --post conditions

  --frame conditions



  Mail.op' = GM
}

-- moveMessage
pred moveMessage [m: Message, mb: Mailbox] {
  --pre conditions

  --post conditions

  --frame conditions


  Mail.op' = MM
}

-- deleteMessage
pred deleteMessage [m: Message] {
  --pre conditions

  --post conditions

  --frame conditions



  Mail.op' = DM
}

-- sendMessage
pred sendMessage [m: Message] {
  --pre conditions

  --post conditions

  --frame conditions



  Mail.op' = SM
}

-- emptyTrash
pred emptyTrash {
  --pre conditions

  --post conditions

  --frame conditions



  Mail.op' = ET
}
/* Note:
   We assume that the spec implicitly meant that the messages are not just
   marked as Purged but are also actually removed from the trash mailbox.
*/

-- createMailbox
pred createMailbox [mb: Mailbox] {
  --pre conditions

  --post conditions

  --frame conditions
 


  Mail.op' = CMB
}

-- deleteMailbox
pred deleteMailbox [mb: Mailbox] {
  --pre conditions

  --post conditions

  --frame conditions



  Mail.op' = DMB
}

-- noOp
pred noOp {
  --pre conditions

  --post conditions

  --frame conditions

  noStatusChange[Message]
  noMessageChange[Mailbox]
  noUserboxChange
  Mail.op' = none 
}

---------------------------
-- Initial state predicate
---------------------------

pred Init {
  -- There are no active or purged messages anywhere


  -- The system mailboxes are all distinct


  -- All mailboxes anywhere are empty


  -- The set of user-created mailboxes is empty


  -- [Keep this tracking constraint intact]
  -- no operator generates the initial state
  Mail.op = none
}

------------------------
-- Transition predicate
------------------------

/** Do not modify! **/
pred Trans {
  // (some mb: Mailbox | createMailbox [mb])
  // or
  // (some mb: Mailbox | deleteMailbox [mb])
  // or
  // (some m: Message | createMessage [m])
  // or  
  // (some m: Message | getMessage [m])
  // or
  // (some m: Message | sendMessage [m])
  // or   
  // (some m: Message | deleteMessage [m])
  // or 
  // (some m: Message | some mb: Mailbox | moveMessage [m, mb])
  // or 
  // emptyTrash
  // or 
  noOp
}


----------
-- Traces
----------

-- Restricts the set of traces to all and only the executions of the Mail app

/** Do not modify! **/
fact System {
  -- traces must satisfy initial state condition and the transition condition
  Init and always Trans
}


run {} for 10

---------------------
-- Sanity check runs
---------------------

pred T1 {
  -- Eventually some message becomes active

}
run T1 for 1 but 8 Object

pred T2 {
  -- The inbox contains more than one message at some point

}
run T2 for 1 but 8 Object

pred T3 {
  -- The trash mailbox eventually contains messages and
  -- becomes empty some time later

}
run T3 for 1 but 8 Object

pred T4 {
  -- Eventually some message in the drafts mailbox moves to the sent mailbox

}
run T4 for 1 but 8 Object

pred T5 {
  -- Eventually there is a user mailbox with messages in it

}
run T5 for 1 but 8 Object 

pred T6 {
  -- Eventually the inbox gets two messages in a row from outside

}
run T6 for 1 but 8 Object

pred T7 {
  -- Eventually some user mailbox gets deleted

}
run T7 for 1 but 8 Object

pred T8 {
  -- Eventually the inbox has messages

  -- Every message in the inbox at any point is eventually removed 

}
run T8 for 1 but 8 Object

pred T9 {
  -- The trash mail box is emptied of its messages eventually

}
run T9 for 1 but 8 Object

pred T10 {
  -- Eventually an external message arrives and 
  -- after that nothing happens anymore

}
run T10 for 1 but 8 Object

run allTests {
  T1 T2 T3 T4 T5 T6 T7 T8 T9 T10
} for 5 but 11 Object, 12 steps 



-----------------------------
-- Expected Valid Properties
-----------------------------

assert V1 {
--  Every active message in the system is in one of the app's mailboxes 

}
check V1 for 5 but 11 Object

 
assert V2 {
--  Inactive messages are in no mailboxes at all

}
check V2 for 5 but 11 Object

assert V3 {
-- Each of the user-created mailboxes differs from the predefined mailboxes

}
check V3 for 5 but 11 Object

assert V4 {
-- Every active message was once external or fresh.

}
check V4 for 5 but 11 Object

assert V5 {
-- Every user-created mailbox starts empty.

}
check V5 for 5 but 11 Object

assert V6 {
-- User-created mailboxes stay in the system indefinitely or until they are deleted.

}
check V6 for 5 but 11 Object

assert V7 {
-- Messages are sent exclusively from the draft mailbox 

}
check V7 for 5 but 11 Object

assert V8 {
-- The app's mailboxes contain only active messages

}
check V8 for 5 but 11 Object

assert V9 {
-- Every received message goes through the inbox

}
check V9 for 5 but 11 Object

assert V10 {
-- Purged message are purged forever

}
check V10 for 5 but 11 Object

assert V11 {
-- No messages in the system can ever (re)acquire External status

}
check V11 for 5 but 11 Object

assert V12 {
-- The trash mailbox starts empty and stays so until a message is delete, if any

}
check V12 for 5 but 11 Object

assert V13 {
-- To purge an active message one must first delete the message 
-- or delete the mailbox that contains it.

}
check V13 for 5 but 11 Object

assert V14 {
-- Every message in the trash mailbox mailbox is there 
-- because it had been previously deleted

}
check V14 for 5 but 11 Object

assert Extra15 {
-- Every message in a user-created mailbox ultimately comes from a system mailbox.

}
check Extra15 for 5 but 11 Object

assert Extra16 {
-- A purged message that was never in the trash mailbox must have been 
-- in a user mailbox that was later deleted

}
check Extra16 for 5 but 11 Object


-------------------------------
-- Expected possible scenarios
-------------------------------

-- It is possible for messages to stay in the inbox indefinitely
-- Negated into: 
assert I1 {

}
check I1 for 5 but 11 Object

-- A message in the sent mailbox need not be there because it was sent.
-- Negated into: 
assert I2 {

}
check I2 for 5 but 11 Object

-- A message that leaves the inbox may later reappear there.
-- Negated into:
assert I3 {

}
check I3 for 5 but 11 Object

-- A deleted message may go back to the mailbox it was deleted from.
-- Negated into:
assert I4 {

}
check I4 for 5 but 11 Object

-- Some external messages may never be received
-- Negated into:
assert I5 {

}
check I5 for 5 but 11 Object

-- A deleted mailbox may reappear in the system
-- Negated into:
assert I6 {

}
check I6 for 5 but 11 Object

-- It is possible to reach a point 
-- where none of the system mailboxes change content anymore
-- Negated into: 
assert I7 {

}
check I7 for 5 but 11 Object

-- Just deleting a message does not guarantee that it gets eventually purged
-- Negated into: 
assert I8 {

}
check I8 for 5 but 11 Object
