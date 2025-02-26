//------------------------------------------------------Interface------------------------------------------------------//
`timescale 1ns/1ps
interface arb_if(
    input bit clk
);
    bit asyn_rst_n;
    logic load, en;
    logic [4:0] data_in;
    logic [4:0] counter;

    // Clocking Block for Testbench
    clocking cb @(posedge clk);
        default input #1 output #2;
        output load;
        input counter;
    endclocking

    // Clocking Block for Monitor
    clocking cb1 @(posedge clk);
        default input #1 output #2;
        input load;
        input counter;
    endclocking

    // Testbench modport
    modport TEST(
        clocking cb,
        output en, asyn_rst_n,
        output data_in
    );

    // DUT modport
    modport DUT(
        input clk, asyn_rst_n, load, en, data_in,
        output counter
    );

    // Monitor modport
    modport MONITOR(
        clocking cb1,
        input load, counter, 
        input clk, asyn_rst_n, en, data_in
    );
endinterface

//------------------------------------------------------5-bit counter------------------------------------------------------//
module counter(arb_if.DUT arbif);
    always_ff @(posedge arbif.clk or negedge arbif.asyn_rst_n) begin
        if(!arbif.asyn_rst_n) begin
            arbif.counter <= 5'b0;
        end
        else begin
            if(arbif.load) begin
                arbif.counter <= arbif.data_in;
            end
            else if(arbif.en) begin
                arbif.counter <= arbif.counter + 1'b1;
            end
            else begin
                arbif.counter <= arbif.counter;
            end
        end
    end
endmodule


//------------------------------------------------------Testbench------------------------------------------------------//
module counter_tb(arb_if.TEST arbif);

    initial begin
        // Initialize the inputs
        arbif.asyn_rst_n <= 1'b0; arbif.cb.load <= 1'b0; arbif.en <= 1'b0; arbif.data_in <= 5'b0;

        // Test case 1
        $display("--------------------Test case 1 - Normal flow--------------------");
      	@(arbif.cb); arbif.asyn_rst_n <= 1'b1; arbif.en <= 1'b1;
        repeat(10) @(arbif.cb);

        // Test case 2
        $display("--------------------Test case 2 - Load new value--------------------");
        @(arbif.cb); arbif.asyn_rst_n <= 1'b1; arbif.cb.load <= 1'b1; arbif.data_in <= 5'b10101;
        @(arbif.cb); arbif.cb.load <= 1'b0;
        repeat(5) @(arbif.cb);

        // Test case 3
        $display("--------------------Test case 3 - Enable--------------------");
        @(arbif.cb); arbif.en <= 1'b0;
        repeat(5) @(arbif.cb); arbif.en <= 1'b1;
        repeat(10) @(arbif.cb);

        // Test case 4
        $display("--------------------Test case 4 - Reset--------------------");
        @(arbif.cb); arbif.asyn_rst_n <= 1'b0;
        repeat(10) @(arbif.cb); arbif.asyn_rst_n <= 1'b1;

        // Test case 5
        $display("--------------------Test case 5 - Roll over--------------------");
        @(arbif.cb); arbif.asyn_rst_n <= 1'b1; arbif.en <= 1'b1; arbif.cb.load <= 1'b1; arbif.data_in <= 5'b11100;
        @(arbif.cb); arbif.cb.load <= 1'b0;
        repeat(10) @(arbif.cb);

        $finish;
    end
endmodule
//------------------------------------------------------Monitor------------------------------------------------------//

module monitor(arb_if.MONITOR arbif);
  	always @(arbif.cb1) begin
        $display("[Time: %0t] Reset: %b, Load: %b, Enable: %b, Data In: %0d || Counter: %0d", $time, arbif.asyn_rst_n, arbif.cb1.load, arbif.en, arbif.data_in, arbif.cb1.counter);
    end
endmodule

//------------------------------------------------------Top Module------------------------------------------------------//
module top;
    bit clk;

    // Generate clock
    initial begin
        clk = 0;
        // Generate waveform
        $dumpfile("dump.vcd");
        $dumpvars;
    end

    always #10 clk = ~clk;
    // Interface
    arb_if arbif(clk);

    // Testbench
    counter_tb tb(arbif.TEST);

    // DUT
    counter uut(arbif.DUT);

    // Monitor
    monitor mon(arbif.MONITOR);
endmodule