import Vector::*;
import BuildVector :: * ;
import CompletionBuffer :: * ;
import GetPut::*;
import Connectable :: * ;

typedef 32 WidthWord;
typedef Bit#(WidthWord) Word;

typedef 8 BuffSize;
typedef CBToken#(BuffSize) Token;

typedef Tuple2#(Token, Word) TWord;

interface ComputeUnit;
    method Action set(TWord val);
    method ActionValue#(TWord) get();
endinterface

interface Arbiter;
    method Action set(Word val);

    method ActionValue#(TWord) getLeft();
    method ActionValue#(TWord) getRight();

    method Action complete(TWord data);
    method ActionValue#(Word) get();
endinterface

module mkComputeUnit(ComputeUnit);
    Reg#(Word) timer <- mkReg(0);
    Reg#(Maybe#(TWord)) val <- mkReg(tagged Invalid);

    rule decrease_timer if (timer > 0);
        timer <= timer - 1;
    endrule

    method Action set(TWord ival) if (timer == 0 && !isValid(val));
        timer <= tpl_2(ival);
        val <= tagged Valid ival;
    endmethod

    method ActionValue#(TWord) get() if (timer == 0 && isValid(val));
        val <= tagged Invalid;
        return fromMaybe(?, val);
    endmethod
endmodule

module mkStaticArbiter(Arbiter);
    Reg#(Maybe#(Word)) data <- mkReg(tagged Invalid);
    Reg#(Bool) direction <- mkReg(False);
    CompletionBuffer#(BuffSize, Word) cbuff <- mkCompletionBuffer;

    method Action set(Word val) if (!isValid(data));
        data <= tagged Valid val;
    endmethod

    method ActionValue#(TWord) getLeft() if (isValid(data) && direction == False);
        let tok <- cbuff.reserve.get;
        data <= tagged Invalid;
        direction <= !direction;
        return tuple2(tok, fromMaybe(?, data));
    endmethod

    method ActionValue#(TWord) getRight() if (isValid(data) && direction == True);
        let tok <- cbuff.reserve.get;
        data <= tagged Invalid;
        direction <= !direction;
        return tuple2(tok, fromMaybe(?, data));
    endmethod

    method Action complete(TWord cdata);
        cbuff.complete.put(cdata);
    endmethod

    method ActionValue#(Word) get();
        let val <- cbuff.drain.get;
        return val;
    endmethod
endmodule

module mkDynamicArbiter(Arbiter);
    Reg#(Maybe#(Word)) data <- mkReg(tagged Invalid);
    CompletionBuffer#(BuffSize, Word) cbuff <- mkCompletionBuffer;

    method Action set(Word val) if (!isValid(data));
        data <= tagged Valid val;
    endmethod

    method ActionValue#(TWord) getLeft() if (isValid(data));
        let tok <- cbuff.reserve.get;
        data <= tagged Invalid;
        return tuple2(tok, fromMaybe(?, data));
    endmethod

    method ActionValue#(TWord) getRight() if (isValid(data));
        let tok <- cbuff.reserve.get;
        data <= tagged Invalid;
        return tuple2(tok, fromMaybe(?, data));
    endmethod

    method Action complete(TWord cdata);
        cbuff.complete.put(cdata);
    endmethod

    method ActionValue#(Word) get();
        let val <- cbuff.drain.get;
        return val;
    endmethod
endmodule

module mkTestBench#(Bool t)();

    Reg#(Word) cycle <- mkReg(0);
    Reg#(Vector#(20, Word)) inputs <- mkReg(vec(100, 10, 100, 10, 100, 10, 100, 10, 100, 10, 100, 10, 100, 10, 100, 10, 100, 10, 100, 10));
    Reg#(Vector#(20, Word)) outputs <- mkReg(newVector());
    Reg#(Word) input_num <- mkReg(0);
    Reg#(Word) output_num <- mkReg(0);
    Arbiter arb <- t ? mkStaticArbiter : mkDynamicArbiter;
    ComputeUnit left <- mkComputeUnit;
    ComputeUnit right <- mkComputeUnit;

    mkConnection(arb.getLeft, left.set);
    mkConnection(arb.getRight, right.set);
    mkConnection(left.get, arb.complete);
    mkConnection(right.get, arb.complete);

    rule cycle_count;
        cycle <= cycle + 1;
    endrule

    rule enq if (input_num < 20);
        arb.set(inputs[input_num]);
        input_num <= input_num + 1;
    endrule

    rule drain if (output_num < 20);
        let val <- arb.get();
        let v = outputs;
        v[output_num] = val;
        outputs <= v;
        output_num <= output_num + 1;
    endrule

    rule finish if (output_num == 20);
        $display("Finished(", $format("%0d", cycle), "): ", fshow(outputs));
        $finish;
    endrule

endmodule

module mkStaticTestBench();
    mkTestBench(True);
endmodule

module mkDynamicTestBench();
    mkTestBench(False);
endmodule
