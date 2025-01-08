//------------------------------------------------------Interface------------------------------------------------------//
interface arb_if(
    input bit clk
);
    bit asyn_rst_n;
    logic load, en;
    logic [5:0] data;
    logic dir;

    // Testbench modport
    modport TEST(
        input clk,
        output asyn_rst_n, load, en,
        input data,
        input dir
    );

    // DUT modport
    modport DUT(
        input clk, asyn_rst_n, load, en, 
        inout data,
        input dir
    );

    // Monitor modport
    modport MONITOR(
        input clk, asyn_rst_n, load, en, data
    );  
endinterface

//------------------------------------------------------5-bit counter------------------------------------------------------//
module counter(arb_if.DUT arbif);

    logic [5:0] tmp;
    always_ff @(posedge arbif.clk or negedge arbif.asyn_rst_n) begin
        if(!arbif.asyn_rst_n) begin
            arbif.data <= 5'b0;
        end
        else begin
            if(arbif.load && !arbif.dir) begin
                tmp <= arbif.data;
            end
            else if(arbif.en && arbif.dir) begin
                if(tmp < 5'b11111) begin
                    tmp <= tmp + 1'b1;
                end
                else if(arbif.data >= 5'b11111) begin
                    arbif.data <= 5'b0;
                end
            end
            else begin
                arbif.data <= arbif.data;
            end
        end
    end
endmodule


//------------------------------------------------------Testbench------------------------------------------------------//
program counter_tb(arb_if.TEST arbif);
    initial begin
        // Initialize the inputs
        arbif.asyn_rst_n = 1'b0; arbif.load = 1'b0; arbif.en = 1'b0; arbif.data = 5'b0; arbif.dir = 1'b0;

        // Test case 1
        $display("--------------------Test case 1 - Normal flow--------------------");
        @(posedge arbif.clk); arbif.asyn_rst_n = 1'b1; arbif.en = 1'b1; arbif.dir = 1'b0;
        @(posedge arbif.clk); arbif.dir = 1'b1;
        repeat(10) @(posedge arbif.clk);

        // Test case 2
        $display("--------------------Test case 2 - Load new value--------------------");
        @(posedge arbif.clk); arbif.asyn_rst_n = 1'b1; arbif.load = 1'b1; arbif.data = 5'b10101; arbif.dir = 1'b0;
        @(posedge arbif.clk); arbif.dir = 1'b1;
        @(posedge arbif.clk); arbif.load = 1'b0;
        repeat(5) @(posedge arbif.clk);

        // Test case 3
        $display("--------------------Test case 3 - Enable--------------------");
        @(posedge arbif.clk); arbif.en = 1'b0;
        repeat(5) @(posedge arbif.clk); arbif.en = 1'b1;
        repeat(10) @(posedge arbif.clk);

        // Test case 4
        $display("--------------------Test case 4 - Reset--------------------");
        @(posedge arbif.clk); arbif.asyn_rst_n = 1'b0;
        repeat(10) @(posedge arbif.clk); arbif.asyn_rst_n = 1'b1;

        // Test case 5
        $display("--------------------Test case 5 - Roll over--------------------");
        @(posedge arbif.clk); arbif.asyn_rst_n = 1'b1; arbif.en = 1'b1; arbif.load = 1'b1; arbif.data = 5'b11100; arbif.dir = 1'b0;
        @(posedge arbif.clk); arbif.dir = 1'b1; arbif.load = 1'b0;
        repeat(10) @(posedge arbif.clk);
    end
endprogram

//------------------------------------------------------Monitor------------------------------------------------------//
module monitor(arb_if.MONITOR arbif);
    always @(posedge arbif.clk) begin
        $display("[Time: %0t] Reset: %b, Load: %b, Enable: %b, Data: %0d ", $time, arbif.asyn_rst_n, arbif.load, arbif.en, arbif.data);
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