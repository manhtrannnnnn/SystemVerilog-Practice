//--------------------------------------------Interface--------------------------------------------//
interface arb_if(
    input bit clk
);
    logic [3:0] a, b;
    bit c;
    logic [4:0] sum;

    // Modport for DUT
    modport DUT(    
        input a, b,
        input c,
        output sum
    );

    // Modport for Testbench
    modport TEST(
        input clk,
        output a, b, c
    );

    // Modport for Monitor
    modport MON(
        input clk,
        input a, b, c, sum
    );
endinterface

//-------------------------------------------- DUT - Full adder 4bit--------------------------------------------//
//-------------------------------------------- DUT - Full adder 4bit--------------------------------------------//
module fulladder(
    input a, b, cin,
    output sum, cout
);
    assign cout = (a & b) | (b & cin) | (cin & a);
    assign sum = a ^ b ^ cin;
endmodule


module adder4bit(arb_if.DUT arbif);
  	assign arbif.sum = arbif.a + arbif.b + arbif.c;
endmodule

//--------------------------------------------Testbench--------------------------------------------//
class Packet;
  	randc logic [3:0] a;
  	rand logic [3:0] b;
    rand bit c;

    constraint val{
        a != b;
    }
endclass

module adder4bit_tb(arb_if.TEST arbif);
    Packet pkg;
    initial begin
        pkg = new(); // Instantiate Packet
      	#500;
      	$finish;
    end

    always_ff @(posedge arbif.clk) begin
      	if(pkg.randomize()) begin
        	arbif.a = pkg.a;
          	arbif.b = pkg.b;
          	arbif.c = pkg.c;
      	end
    end
endmodule

//--------------------------------------------Monitor--------------------------------------------//
module monitor(arb_if.MON arbif);
    logic [4:0] result; 
    int passed = 0;
    int failed = 0;
    assign result = arbif.a + arbif.b + arbif.c;
  	always_ff @(posedge arbif.clk) begin
      	if(arbif.sum != result) begin
            $display("[TIME: %0t] TEST FAILED!!!: With A: %b, B: %b, C: %b || sum: %b || Expected Result: %b", 
                     $time, arbif.a, arbif.b, arbif.c, arbif.sum, result);
            failed++;
        end
        else begin
          	$display("[TIME: %0t] TEST PASSED!!!: With A: %b, B: %b, C: %b || sum: %b || Expected Result: %b", 
                     $time, arbif.a, arbif.b, arbif.c, arbif.sum, result);
            passed++;
        end
    end

    final begin
        if(failed == 0) begin
            $display("================================");
            $display("ALL TEST PASSED");
            $display("================================");
        end
        else begin
            $display("================================");
            $display("TEST FAILED!!!");
            $display("Test passed: %0d", passed);
            $display("Test failed: %0d",failed);
            $display("================================");
        end
    end
endmodule

//--------------------------------------------Top--------------------------------------------//
module top;
    bit clk;
    initial clk = 0;
    always #5 clk = ~clk; // Clock generation with 10-timeunit period

    // Interface
    arb_if arbif(clk);

    // DUT
    adder4bit dut(arbif.DUT);

    // Testbench
    adder4bit_tb tb(arbif.TEST);

    // Monitor
    monitor mon(arbif.MON);
endmodule
