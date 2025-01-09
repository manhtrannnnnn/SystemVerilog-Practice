    //------------------------------------------------------Interface------------------------------------------------------//
    interface arb_if(
        input bit clk
    );
        bit asyn_rst_n;
        logic load, dir;
        wire [4:0] data;

        // Testbench modport
        modport TEST(
            input clk, dir, 
            inout data,
            output asyn_rst_n, load
        );

        // DUT modport
        modport DUT(
            input clk, asyn_rst_n, load, dir,
            inout data
        );

        // Monitor modport
        modport MONITOR(
            input clk, asyn_rst_n, load, data, dir
        );  
    endinterface

    //------------------------------------------------------5-bit counter------------------------------------------------------//
    module counter(arb_if.DUT arbif);
        logic [4:0] data_tmp;
        
        always@(posedge arbif.clk or negedge arbif.asyn_rst_n) begin
            if(!arbif.asyn_rst_n) begin
                data_tmp <= 5'b0;
            end
            else if(arbif.load) begin
                data_tmp <= (arbif.dir) ? arbif.data : 5'bz;
            end
            else begin
                data_tmp <= data_tmp + 1'b1;
            end
        end
        assign arbif.data = (~arbif.dir) ? data_tmp : 5'bz;
    endmodule


    //------------------------------------------------------Testbench------------------------------------------------------//
    program counter_tb(arb_if.TEST arbif);
        logic [5:0] data_drive;
        assign arbif.data = (arbif.dir) ? data_drive : 5'bz;

        initial begin
            // Initialize the inputs
            arbif.asyn_rst_n = 1'b0; arbif.load = 1'b1; data_drive = 5'b0; arbif.dir = 1'b1;

            // Test case 1
            $display("--------------------Test case 1 - Normal flow--------------------");
            @(negedge arbif.clk); arbif.asyn_rst_n = 1'b1; arbif.dir = 1'b1;
            @(negedge arbif.clk); arbif.dir = 1'b0; arbif.load = 1'b0;
            repeat(20) @(negedge arbif.clk);

            // Test case 2
            $display("--------------------Test case 2 - Load new value--------------------");
            @(negedge arbif.clk); arbif.asyn_rst_n = 1'b1; arbif.dir = 1'b1; arbif.load = 1'b1; data_drive = 5'b10001;
            @(negedge arbif.clk); arbif.dir = 1'b0; arbif.load = 1'b0;
            repeat(10) @(negedge arbif.clk);

            // Test case 4
            $display("--------------------Test case 3 - Reset--------------------");
            @(negedge arbif.clk); arbif.asyn_rst_n = 1'b0;
            repeat(10) @(negedge arbif.clk); arbif.asyn_rst_n = 1'b1;

            // Test case 5
            $display("--------------------Test case 4 - Roll over--------------------");
            @(negedge arbif.clk); arbif.asyn_rst_n = 1'b1; arbif.dir = 1'b1; data_drive = 5'b10111; arbif.load = 1'b1;
            @(negedge arbif.clk); arbif.dir = 1'b0; arbif.load = 1'b0;
            repeat(20) @(negedge arbif.clk);
        end
    endprogram

    //------------------------------------------------------Monitor------------------------------------------------------//
    module monitor(arb_if.MONITOR arbif);
        always @(posedge arbif.clk) begin
            $display("[Time: %0t] Reset: %b, Load: %b, Dir: %b Data: %0d ", $time, arbif.asyn_rst_n, arbif.load, arbif.dir, arbif.data);
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