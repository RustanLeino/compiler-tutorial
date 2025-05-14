// The RawMachine is a primitive machine for program execution. Unlike the slightly more
// abstract Machine, RawMachine does not have call stack. Instead, all operations are performed
// on a single evaluation stack. Moreover, while the Machine directly makes use of Variable,
// BasicBlock, and Procedure declarations, the RawMachine instead just uses integer indices
// into the global code area or indices into the global evaluation stack. These indices are
// computed by the Assembler.

module RawMachine {
  export
    provides Util
    reveals Opcode
    provides Opcode.ToString, Opcode.HasArgument
    provides Encode, Decode
    provides Run

  import opened Util

  datatype Opcode =
    | Halt            // HALT: halts execution of the machine
    | Push            // PUSH x: pushes x onto the stack
    | Adjust          // ADJ x: adjusts the stack pointer by x (e.g., ADJ 1 has the effect of popping the top of the stack)
    | Load            // LOAD x: reads the value at offset x from the stack pointer and pushes it onto the stack (e.g.,
                      //         LOAD 1 duplicates the top element)
    | Store           // STOR x: pops the top element of the stack (say: s) and then stores s at offset x from the new stack pointer
    | Jump            // JMP x: sets the program counter to x
    | JumpIndirect    // IJMP: pops the top element of the stack (say: s) and sets the program counter to s
    | ConditionalJump // JMPZ x: pops the top element of the stack (say: s) and, if s==0, sets the program counter to x
    | Subtract        // SUB: replaces the top two elements of the stack (say: s t) with s-t
    | Compare         // CMP: replaces the top two elements of the stack (say: s t) with 1 if s<=t and 0 otherwise
  {
    function ToString(): string {
      match this
      case Halt => "HALT"
      case Push => "PUSH"
      case Adjust => "ADJ"
      case Load => "LOAD"
      case Store => "STOR"
      case Jump => "JMP"
      case JumpIndirect => "IJMP"
      case ConditionalJump => "JMPZ"
      case Subtract => "SUB"
      case Compare => "CMP"
    }

    predicate HasArgument() {
      match this
      case Halt | JumpIndirect | Subtract | Compare => false
      case Push | Adjust | Load | Store | Jump | ConditionalJump => true
    }
  }

  function Encode(op: Opcode): nat {
    match op
    case Halt => 0
    case Push => 1
    case Adjust => 2
    case Load => 3
    case Store => 4
    case Jump => 5
    case JumpIndirect => 6
    case ConditionalJump => 7
    case Subtract => 8
    case Compare => 9
  }

  function Decode(w: int): Option<Opcode> {
    match w
    case 0 => Some(Halt)
    case 1 => Some(Push)
    case 2 => Some(Adjust)
    case 3 => Some(Load)
    case 4 => Some(Store)
    case 5 => Some(Jump)
    case 6 => Some(JumpIndirect)
    case 7 => Some(ConditionalJump)
    case 8 => Some(Subtract)
    case 9 => Some(Compare)
    case _ => None
  }

  lemma EncodeThenDecode(op: Opcode)
    ensures Decode(Encode(op)) == Some(op)
  {
  }

  lemma DecodeThenEncode(w: int)
    requires Decode(w).Some?
    ensures Encode(Decode(w).value) == w
  {
  }

  class RawMachineState {
    const code: seq<int>
    var stack: array<int>
    var pc: int
    var sp: int

    constructor (code: seq<int>)
      ensures fresh(stack)
    {
      this.code := code;
      stack := new int[1000];
      pc, sp := 0, 0;
    }

    method GetCurrentStack() returns (s: seq<int>) {
      if 0 <= sp <= stack.Length {
        return stack[..sp];
      } else if sp < 0 {
        return [];
      } else {
        return stack[..] + seq(sp - stack.Length, _ => 0);
      }
    }

    method PrintMachineState(steps: nat) {
      print "After ", steps, " steps: ";
      print "pc=", Hex(pc), "  ";
      var s := GetCurrentStack();
      print "stack=", seq(|s|, w => Hex(w));
      print "\n";
    }

    method Fetch() returns (r: Result<Opcode>, argument: int)
      modifies this
      ensures stack == old(stack) || fresh(stack)
    {
      if !(0 <= pc < |code|) {
        return Failure("pc out of range"), 0;
      }
      var maybeOpcode := Decode(code[pc]);
      if maybeOpcode == None {
        return Failure("illegal opcode"), 0;
      }
      var op := maybeOpcode.value;
      if op.HasArgument() {
        if pc + 1 == |code| {
          return Failure("pc out of range for argument"), 0;
        }
        argument := code[pc + 1];
        pc := pc + 2;
      } else {
        argument := 0;
        pc := pc + 1;
      }
      return Success(op), argument;
    }

    method Get(stackLocation: int) returns (r: Result<int>) {
      if stackLocation < 0 {
        return Failure("invalid address");
      }
      return Success(if stackLocation < stack.Length then stack[stackLocation] else 0);
    }

    method Set(stackLocation: int, value: int) returns (r: Result<()>)
      modifies this, stack
      ensures stack == old(stack) || fresh(stack)
    {
      if stackLocation < 0 {
        return Failure("invalid address");
      }
      if stack.Length <= stackLocation {
        stack := new int[stackLocation + 1000](i reads this, stack => if 0 <= i < stack.Length then stack[i] else 0);
      }
      stack[stackLocation] := value;
      return Success(());
    }

    method Pop() returns (r: Result<int>)
      modifies this
      ensures stack == old(stack) || fresh(stack)
    {
      sp := sp - 1;
      r := Get(sp);
    }

    method Push(value: int) returns (r: Result<()>)
      modifies this, stack
      ensures stack == old(stack) || fresh(stack)
    {
      var _ :- Set(sp, value);
      sp := sp + 1;
      return Success(());
    }
  }

  // Run the "code", starting at address 0, stopping at a HALT instruction or after
  // "maxSteps" steps. If HALT is reached, returns the stack.
  method Run(code: seq<int>, maxSteps: nat) returns (r: Result<seq<int>>) {
    var machine := new RawMachineState(code);
    for i := 0 to maxSteps
      invariant fresh(machine.stack)
    {
      // machine.PrintMachineState(i);

      var op, argument :- machine.Fetch();
      match op
      case Halt =>
        var s := machine.GetCurrentStack();
        return Success(s);
      case Push =>
        var _ :- machine.Push(argument);
      case Adjust =>
        machine.sp := machine.sp - argument;
      case Load =>
        var value :- machine.Get(machine.sp - argument);
        var _ :- machine.Push(value);
      case Store =>
        var value :- machine.Pop();
        var _ :- machine.Set(machine.sp - argument, value);
      case Jump =>
        machine.pc := argument;
      case JumpIndirect =>
        var value :- machine.Pop();
        machine.pc := value;
      case ConditionalJump =>
        var value :- machine.Pop();
        if value == 0 {
          machine.pc := argument;
        }
      case Subtract =>
        var t :- machine.Pop();
        var s :- machine.Pop();
        var _ :- machine.Push(s - t);
      case Compare =>
        var t :- machine.Pop();
        var s :- machine.Pop();
        var _ :- machine.Push(if s <= t then 1 else 0);
    }
    return Failure("program required too many steps to run");
  }
}