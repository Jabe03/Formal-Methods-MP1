--===============================================
-- CS:5810 Formal Methods in Software Engineering
-- Fall 2023
--
-- Mini Project 1
--
-- Name:  Mitchell Piehl and Josh Bergthold
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
    -- the message cannot already be in a mailbox
  m not in Mailbox.messages
    -- the message needs to be from the set of fresh messages
  m.status = Fresh
  --post conditions
    -- the messages in drafts will all remain the same, but the new message will be added
  Mail.drafts.messages' = Mail.drafts.messages + m
    -- the status of the new message will become active
  m.status' = Active
  --frame conditions
    -- the messages in every mailbox will remain the same besides the draft mailbox
  noMessageChange[Mailbox - Mail.drafts]
    -- the status of every message will remain the same except for the status of the new message
  noStatusChange[Message - m]
    -- the userboxes will not change
  noUserboxChange
  Mail.op' = CM
}

-- getMessage 
pred getMessage [m: Message] {
  --pre conditions
      -- the new message must be external to the system
    m.status = External
      -- the new message must not already be in a mailbox
    no messages.m
  --post conditions
      -- when the new message is recieved, the status becomes active
    m.status' = Active
      -- the messages in the inbox remain the same but the new message gets added
    Mail.inbox.messages' = Mail.inbox.messages + m
  --frame conditions
      -- the messages in every mailbox will remain the same besides the inbox
    noMessageChange[Mailbox - Mail.inbox]
      -- the status of every message will remain the same except for the status of the new message
    noStatusChange[Message - m]
      -- the userboxes will not change
    noUserboxChange


  Mail.op' = GM
}

-- moveMessage
pred moveMessage [m: Message, mb: Mailbox] {
  --pre conditions
    // m in (mb.)
      -- the new mailbox must be in the system
    mb in (Mail.uboxes + Mail.sent + Mail.inbox + Mail.drafts)
    let src_mailbox = messages.m | {
      -- the message must already be in a mailbox
    some src_mailbox
      -- the new mailbox must be different than the old mailbox
    src_mailbox != mb
    // not (m in Mail.trash.messages)
  --post conditions
      -- the new mailbox gains the message being moved
    mb.messages' = mb.messages + m
      -- the old mailbox loses the message being moved
    src_mailbox.messages' = src_mailbox.messages - m 
  --frame conditions
      -- the messages in every mailbox will remain the same besides the old mailbox and the new mailbox
    noMessageChange[Mailbox - (mb + src_mailbox)]
      -- the status of every message will remain the same
    noStatusChange[Message]
      -- the userboxes will not change
    noUserboxChange

  Mail.op' = MM}
}

-- deleteMessage
pred deleteMessage [m: Message] {
  --pre conditions
      -- the message must be in a mailbox
    some messages.m
      -- the message cannot be in the trash already
    Mail.trash != messages.m 
  --post conditions
      -- the trash mailbox gains the new message
    Mail.trash.messages' = Mail.trash.messages + m
     -- the old mailbox loses the message
    messages.m.messages' = messages.m.messages - m 
  --frame conditions
      -- the messages in every mailbox will remain the same besides the old mailbox and trash
    noMessageChange[Mailbox - (Mail.trash + messages.m)]
      -- the status of every message will remain the same
    noStatusChange[Message]
      -- the userboxes will not change
    noUserboxChange

  Mail.op' = DM
}

-- sendMessage
pred sendMessage [m: Message] {
  let src_mailbox = messages.m |{
  --pre conditions
      -- the message must be in drafts
    src_mailbox = Mail.drafts
  --post conditions
      -- the sent mailbox gains the message being sent
    Mail.sent.messages' = Mail.sent.messages + m
      -- the drafts mailbox loses the message being sent
    Mail.drafts.messages' = Mail.drafts.messages - m
  --frame conditions
      -- the messages in every mailbox will remain the same besides the sent mailbox and drafts mailbox
    noMessageChange[Mailbox - (Mail.sent + Mail.drafts)]
      -- the status of every message will remain the same
    noStatusChange[Message]
      -- the userboxes will not change
    noUserboxChange

  Mail.op' = SM
  }
}
run {eventually (some m:Message | sendMessage[m])} for 10

-- emptyTrash
pred emptyTrash {
  --pre conditions
      -- the trash must have some messages
    some Mail.trash.messages
  --post conditions
      -- the status of all messages in trash becomes purged
    all m : Mail.trash.messages | m.status' = Purged
    // no Mail.trash.messages'
      -- after emptying the trash, there will be no messages in trash
    after no Mail.trash.messages
  --frame conditions
     -- the messages in every mailbox will remain the same besides the trash mailbox
    noMessageChange[Mailbox - Mail.trash]
      -- the status of every message will remain the same besides the messages in trash
    noStatusChange[Message - Mail.trash.messages]
      -- the userboxes will not change
    noUserboxChange


  Mail.op' = ET
}
/* Note:
   We assume that the spec implicitly meant that the messages are not just
   marked as Purged but are also actually removed from the trash mailbox.
*/

-- createMailbox
pred createMailbox [mb: Mailbox] {
  --pre conditions
      -- the new mailbox cannot already be in the system
    mb not in (Mail.uboxes + Mail.trash + Mail.sent + Mail.inbox + Mail.drafts)
  --post conditions
      -- the new mailbox will be added to uboxes
    Mail.uboxes' = Mail.uboxes + mb
  --frame conditions
      -- the messages in every mailbox will remain the same
    noMessageChange[Mailbox]
      -- the status of every message will remain the same
    noStatusChange[Message]

  Mail.op' = CMB
}

-- deleteMailbox
pred deleteMailbox [mb: Mailbox] {
  --pre conditions
      -- the mailbox being deleted must be in uboxes
    mb in (Mail.uboxes)
  --post conditions
      -- the status of every message in the deleted mailbox will be purged
    all m : mb.messages | m.status' = Purged
      -- afterwards, the deleted mailbox will not the in uboxes
    Mail.uboxes' = Mail.uboxes - mb
      -- afterwards, there will be no messages in the mailbox that is being deleted
    mb.messages' = mb.messages - mb.messages
  --frame conditions
      -- the messages in every mailbox will remain the same besides the mailbox being deleted
    noMessageChange[Mailbox - mb]
      -- the status of every message will remain the same besides the messages in the deleted mailbox
    noStatusChange[Message - mb.messages]



  Mail.op' = DMB
}
run {eventually some mb : Mailbox | eventually (createMailbox[mb] and eventually ((some m: Message| moveMessage[m, mb]) and eventually deleteMailbox[mb]))} for 10


-- noOp
pred noOp {
  --pre conditions

  --post conditions

  --frame conditions
    -- the status of every message will remain the same
  noStatusChange[Message]
    -- the messages in every mailbox will remain the same
  noMessageChange[Mailbox]
    -- the userboxes will not change
  noUserboxChange
  Mail.op' = none 
}

---------------------------
-- Initial state predicate
---------------------------

pred Init {
  -- There are no active or purged messages anywhere
	no m: Message | some m.status and m.status in (Purged + Active)

  -- The system mailboxes are all distinct
	#(Mail.inbox + Mail.drafts + Mail.trash + Mail.sent) = 4

  -- All mailboxes anywhere are empty
	all m : Mailbox | no m.messages 

  -- The set of user-created mailboxes is empty
	no Mail.uboxes

  -- [Keep this tracking constraint intact]
  -- no operator generates the initial state
  Mail.op = none
}


------------------------
-- Transition predicate
------------------------

/** Do not modify! **/
pred Trans {
  (some mb: Mailbox | createMailbox [mb])
  or
  (some mb: Mailbox | deleteMailbox [mb])
  or
  (some m: Message | createMessage [m])
  or  
  (some m: Message | getMessage [m])
  or
  (some m: Message | sendMessage [m])
  or   
  (some m: Message | deleteMessage [m])
  or 
  (some m: Message | some mb: Mailbox | moveMessage [m, mb])
  or 
  emptyTrash
  or 
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


run {eventually (some m:Message | createMessage[m])} for 10

---------------------
-- Sanity check runs
---------------------

pred T1 {
  -- Eventually some message becomes active TODO: IMPLEMENT STATUSES
    eventually (some m:Message | m.status = Active)
}
run T1 for 1 but 8 Object

pred T2 {
  -- The inbox contains more than one message at some point
  eventually #(Mail.inbox.messages) > 1
}
run T2 for 1 but 8 Object

pred T3 {
  -- The trash mailbox eventually contains messages and
  -- becomes empty some time later
    eventually (some Mail.trash.messages and after (eventually no Mail.trash.messages))
}
run T3 for 1 but 8 Object

pred T4 {
  -- Eventually some message in the drafts mailbox moves to the sent mailbox
  eventually (some m : Message | messages.m = Mail.drafts and after (eventually (messages.m = Mail.sent)))
}
run T4 for 1 but 8 Object

pred T5 {
  -- Eventually there is a user mailbox with messages in it
    eventually (some mb : (Mail.uboxes) | some mb.messages)
}
run T5 for 1 but 8 Object 

pred T6 {
  -- Eventually the inbox gets two messages in a row from outside
  some m1, m2 : Message | m1 != m2 and eventually (getMessage[m1] and after getMessage[m2])
}
run T6 for 1 but 8 Object

pred T7 {
  -- Eventually some user mailbox gets deleted
    eventually (some mb : (Mail.uboxes) | deleteMailbox[mb])
}
run T7 for 1 but 8 Object

pred T8 {
  -- Eventually the inbox has messages
  eventually some Mail.inbox.messages
  -- Every message in the inbox at any point is eventually removed 
  always (all m : Message | messages.m = Mail.inbox implies eventually (messages.m != Mail.inbox))
}
run T8 for 1 but 8 Object

pred T9 {
  -- The trash mail box is emptied of its messages eventually
  eventually emptyTrash
}
run T9 for 1 but 8 Object

pred T10 {
  -- Eventually an external message arrives and 
  -- after that nothing happens anymore
  eventually (some m : Message | getMessage[m] and after always noOp)
}
run T10 for 1 but 8 Object

-- NOTE TO GRADER: We believe that T10 and T8 are contradictory, as T8 states that every message in the inbox is removed at some point,
-- while T10 states that eventually an external message arrives and after that nothing happens anymore, meaning the message in the inbox is never removed.
-- So allTests will not pass so long as T8 and T10 are both included.
-- FURTHER NOTE: T10 seems to also be contradicting other tests, probably because it requires noOps as the only
-- transition for the tail-end of the trace. Otherwise, T1-T9 conjunctively pass. 
run allTests {
  T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 --T10 is a problem
} for 5 but 11 Object, 12 steps 



-----------------------------
-- Expected Valid Properties
-----------------------------

assert V1 {
--  Every active message in the system is in one of the app's mailboxes 
  always (all m : {x : Message | x.status = Active} | 
          let sys_mailboxes = sboxes + Mail.uboxes |
            some mb : sys_mailboxes | m in mb.messages)
}
check V1 for 5 but 11 Object

 
assert V2 {
--  Inactive messages are in no mailboxes at all
  always (all m : Message | m.status != Active implies no messages.m)
}
check V2 for 5 but 7 Object

assert V3 {
-- Each of the user-created mailboxes differs from the predefined mailboxes
  always (no sboxes & Mail.uboxes)
}
check V3 for 5 but 11 Object

assert V4 {
-- Every active message was once external or fresh.
  always (all m : Message | m.status = Active implies once (m.status = Fresh or m.status = External))
}
check V4 for 5 but 11 Object

assert V5 {
-- Every user-created mailbox starts empty.
  always (all mb : Mailbox | createMailbox[mb] implies after no mb.messages)
}
check V5 for 5 but 11 Object

assert V6 {
-- User-created mailboxes stay in the system indefinitely or until they are deleted.
  always (all m : Mailbox | m in Mail.uboxes implies deleteMailbox[m] or after (m in Mail.uboxes))
}
check V6 for 5 but 11 Object

assert V7 {
-- Messages are sent exclusively from the draft mailbox 
  always (all m : Message | sendMessage[m] implies messages.m = Mail.drafts)
}
check V7 for 5 but 11 Object

assert V8 {
-- The app's mailboxes contain only active messages
    always (all m : Message | m in sboxes.messages or m in Mail.uboxes.messages implies m.status = Active )
}
check V8 for 5 but 9 Object

assert V9 {
-- Every received message goes through the inbox
  always (all m : Message | getMessage[m] implies after messages.m = Mail.inbox)
}
check V9 for 5 but 11 Object

assert V10 {
-- Purged message are purged forever
  always (all m : Message | m.status = Purged implies always m.status = Purged )
}
check V10 for 5 but 11 Object

assert V11 {
-- No messages in the system can ever (re)acquire External status
  always all m : {x : Message | x.status = External} | 
    (always m.status = External) or  
    eventually {
      not m.status = External 
      after always not m.status = External
    }

}
check V11 for 5 but 11 Object

assert V12 {
-- The trash mailbox starts empty and stays so until a message is delete, if any
  no Mail.trash.messages and (some Mail.trash.messages implies (some m : Message | deleteMessage[m]))
  
}
check V12 for 5 but 11 Object

assert V13 {
-- To purge an active message one must first delete the message 
-- or delete the mailbox that contains it.
  always (all m : Message | (m.status = Active and after (m.status = Purged)) implies (
    once deleteMessage[m] and emptyTrash
    or
    deleteMailbox[messages.m]
  ))
}
check V13 for 5 but 11 Object

assert V14 {
-- Every message in the trash mailbox mailbox is there 
-- because it had been previously deleted
  always (all m : Message | m in Mail.trash.messages implies once deleteMessage[m] )


}
check V14 for 5 but 7 Object

assert Extra15 {
-- Every message in a user-created mailbox ultimately comes from a system mailbox.
always (all m : {x:Message | (some messages.x) and messages.x in Mail.uboxes} |
        once m in sboxes.messages)
}
check Extra15 for 5 but 11 Object

assert Extra16 {
-- A purged message that was never in the trash mailbox must have been 
-- in a user mailbox that was later deleted
   always (all m : Message | some mb : Mailbox | (m.status = Purged and not (once m in Mail.trash.messages) and once messages.m = mb) implies (once deleteMailbox[mb]))
}
check Extra16 for 5 but 11 Object


-------------------------------
-- Expected possible scenarios
-------------------------------

-- It is possible for messages to stay in the inbox indefinitely
-- Negated into: There is no message that stays in the inbox indefinitely
assert I1 {
   no m : Message | eventually (always (m in Mail.inbox.messages))
}
check I1 for 5 but 11 Object

-- A message in the sent mailbox need not be there because it was sent.
-- Negated into: A message in the sent mailbox needs to be there because it was sent
assert I2 {
   always (all m : Message | m in Mail.sent.messages implies once sendMessage[m])
}
check I2 for 5 but 11 Object

-- A message that leaves the inbox may later reappear there.
-- Negated into: Once a message leaves the inbox, it will never appear there again
assert I3 {
    no m: Message | eventually {
     m in Mail.inbox.messages
     after (not m in Mail.inbox.messages)
     after (eventually m in Mail.inbox.messages)
    }
}
check I3 for 5 but 11 Object

-- A deleted message may go back to the mailbox it was deleted from.
-- Negated into: A deleted message may never go back to the mailbox it was deleted from
assert I4 {
  always (all m : Message | all Mb : Mailbox | messages.m = Mail.trash and once messages.m = Mb and Mb != Mail.trash implies not eventually (messages.m != Mail.trash and messages.m = Mb ))
}
check I4 for 5 but 11 Object

-- Some external messages may never be received
-- Negated into: All external messages are eventually received
assert I5 {
  all m : {x : Message | x.status = External} | eventually getMessage[m]
}
check I5 for 5 but 11 Object

-- A deleted mailbox may reappear in the system
-- Negated into: A deleted mailbox may not reappear in the system
assert I6 {
  always (all mb : Mailbox | once (mb in Mail.uboxes) and mb not in Mail.uboxes implies not eventually mb in Mail.uboxes )
}
check I6 for 5 but 11 Object

-- It is possible to reach a point 
-- where none of the system mailboxes change content anymore
-- Negated into: The system mailboxes will always eventually change in their content
assert I7 {
  always all mb : (Mail.trash + Mail.sent + Mail.drafts + Mail.inbox) |
        eventually (mb.messages != mb.messages')
}
check I7 for 5 but 11 Object

-- Just deleting a message does not guarantee that it gets eventually purged
-- Negated into: Deleting a message guarantees that it eventually gets purged
assert I8 {
  always (all m : Message | messages.m = Mail.trash implies eventually m.status = Purged )
}
check I8 for 5 but 11 Object
