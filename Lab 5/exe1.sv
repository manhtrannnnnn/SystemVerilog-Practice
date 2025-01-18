//----------------------------------------------Parallel In Parallel Out(PISO)----------------------------------------------//
module piso(
    input logic clk, rst_n,
    input logic load, en,
    input logic [7:0] data_in,
    output logic data_out
);

    logic [7:0] shift_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if(!rst_n) begin
            data_out <= 1'b0;
            shift_reg <= 8'b0;
        end
        else begin
            if(load) begin
                shift_reg <= data_in;
                data_out <= data_out;
            end
            else if(en) begin
                shift_reg <= {shift_reg[0], shift_reg[7:1]};
                data_out <= shift_reg[0];
            end
        end
    end
endmodule


//----------------------------------------Test bench----------------------------------------//
module piso_tb(
    input logic clk, 
    output logic rst_n,
    output logic load, en,
    output logic [7:0] data_in,
    input logic data_out
);
    // Test stimulus 
    initial begin
        // Initialize data
        @(posedge clk); rst_n = 1'b0; load = 1'b0; en = 1'b0; data_in = 8'b0; 

        // Test normal flow
        $display("--------------------Test normal flow - 10101111--------------------");
        @(posedge clk); rst_n = 1'b1; load = 1'b1; en = 1'b1; data_in = 8'b10101111;
        @(posedge clk); load = 1'b0;
        repeat(10) @(posedge clk);

        // Test load
        $display("--------------------Test load new value - 11101100--------------------");
        @(posedge clk); rst_n = 1'b1; load = 1'b1; en = 1'b1; data_in = 8'b11101100;
        @(posedge clk); load = 1'b0;
        repeat(10) @(posedge clk);

        // Test enable
        $display("--------------------Test enable - 11101111--------------------");
        @(posedge clk); rst_n = 1'b1; load = 1'b1; en = 1'b1; data_in = 8'b11101111;
        @(posedge clk); load = 1'b0; en = 1'b0;
        repeat(10) @(posedge clk); en = 1'b1;
        repeat(10) @(posedge clk); en = 1'b0;

        // Test reset
        $display("--------------------Test reset - 11101110--------------------");
        @(posedge clk); rst_n = 1'b1; load = 1'b1; en = 1'b1; data_in = 8'b11101110;
        @(posedge clk); load = 1'b0; en = 1'b0; rst_n = 1'b0;
        repeat(10) @(posedge clk);
        $finish;
    end

    // Monitor
    initial begin
        forever begin
            @(posedge clk);
             $display("[TIME: %0t] data_out: %0d" ,$time, data_out);
        end
    end

    // Generate waveform
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end
endmodule


//----------------------------------------Testbench using program block----------------------------------------//
program piso_tb(
    input logic clk, 
    output logic rst_n,
    output logic load, en,
    output logic [7:0] data_in,
    input logic data_out
);
    // Test stimulus 
    initial begin
        // Initialize data
        @(posedge clk); rst_n = 1'b0; load = 1'b0; en = 1'b0; data_in = 8'b0; 

        // Test normal flow
        $display("--------------------Test normal flow - 10101111--------------------");
        @(posedge clk); rst_n = 1'b1; load = 1'b1; en = 1'b1; data_in = 8'b10101111;
        @(posedge clk); load = 1'b0;
        repeat(10) @(posedge clk);

        // Test load
        $display("--------------------Test load new value - 11101100--------------------");
        @(posedge clk); rst_n = 1'b1; load = 1'b1; en = 1'b1; data_in = 8'b11101100;
        @(posedge clk); load = 1'b0;
        repeat(10) @(posedge clk);

        // Test enable
        $display("--------------------Test enable - 11101111--------------------");
        @(posedge clk); rst_n = 1'b1; load = 1'b1; en = 1'b1; data_in = 8'b11101111;
        @(posedge clk); load = 1'b0; en = 1'b0;
        repeat(10) @(posedge clk); en = 1'b1;
        repeat(10) @(posedge clk); en = 1'b0;

        // Test reset
        $display("--------------------Test reset - 11101110--------------------");
        @(posedge clk); rst_n = 1'b1; load = 1'b1; en = 1'b1; data_in = 8'b11101110;
        @(posedge clk); load = 1'b0; en = 1'b0; rst_n = 1'b0;
        repeat(10) @(posedge clk);
        $finish;
    end

    // Monitor
    initial begin
        forever begin
            @(posedge clk);
             $display("[TIME: %0t] data_out: %0d" ,$time, data_out);
        end
    end

    // Generate waveform
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end
endprogram

//----------------------------------------Top Module----------------------------------------//
module top;
    logic clk, rst_n, load, en;
    logic [7:0] data_in;
    logic data_out;

    // Generate clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Testbench 
    piso_tb tb(
        .clk(clk),
        .rst_n(rst_n),
        .load(load),
        .en(en),
        .data_in(data_in),
        .data_out(data_out)
    );

    // DUT
    piso uut(
        .clk(clk),
        .rst_n(rst_n),
        .load(load),
        .en(en),
        .data_in(data_in),
        .data_out(data_out)
    );
endmodule

