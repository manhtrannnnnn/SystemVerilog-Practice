//----------------------------Last In First Out--------------------------------//
module lifo(
    input clk, 
    input [7:0] data_in, 
    input wr_en, rd_en,
    output empty, full,
    output logic [7:0] data_out
);

    logic [7:0] mem [$:15];
    always_ff @(posedge clk) begin
        if(wr_en) begin
            mem.push_front(data_in);
        end
        if(rd_en) begin
            data_out = mem.pop_front();
        end
    end
    assign empty = (mem.size() == 0);
    assign full = (mem.size() == 16);
endmodule

//----------------------------Verify LIFO--------------------------------//
module lifo_tb;
    // Declare inputs
    reg clk, wr_en, rd_en;
    reg [7:0] data_in;
    // Declare outputs
    wire empty, full;
    wire [7:0] data_out;
    parameter CLK_PERIOD = 20;

    // Instantiate the Unit Under Test (UUT)
    lifo uut (
        .clk(clk), 
        .data_in(data_in), 
        .wr_en(wr_en), 
        .rd_en(rd_en),
        .empty(empty), 
        .full(full), 
        .data_out(data_out)
    );

    // Initialize Inputs
    initial begin
      // Testing write full to memory
        $display("-----------------Write Full to Memory-----------------");
        repeat(16) write_data();

        // Read empty from memory
        $display("-----------------Read Full from Memory-----------------");
        repeat(20) read_data();
      	
        // Read from Memory after Write to it
        $display("-----------------Read from Memory after Write to it-----------------");
        repeat(8) write_data();
        repeat(5) read_data();

        // Write and Read simultaneously
        $display("-----------------Write and Read Data-----------------");
        fork
            begin
                repeat(13) write_data();
            end
            begin
              	repeat(16) read_data();
            end
        join
        

        #CLK_PERIOD;
      	$finish;
    end

    // Write data to LIFO
    task write_data();
        wr_en = 1;
        data_in = $random % 256;
        #CLK_PERIOD;
        wr_en = 0;
    endtask

    // Read data from LIFO
    task read_data();
        rd_en = 1;
        #CLK_PERIOD;
        rd_en = 0;
    endtask

    // Clock generation
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end

    // Monitor
    initial begin
        $monitor("[TIME=%0t] data_in=%h || data_out=%h, empty=%b, full=%b", $time, data_in, data_out, empty, full);
    end

    // Generate Waveform
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end

endmodule