//------------------------------- Mux 8x1 using logic and unique case statement -------------------------------//
module mux8to1(
    input  [7:0] data_in,
    input  [2:0] sel,
    output logic data_out
);
    always_comb begin  
        // Kiểm tra giá trị của 'sel' có nằm trong phạm vi hợp lệ hay không
        if (sel inside {[3'b000:3'b111]}) begin
            unique case (sel)
                3'b000: data_out = data_in[0];
                3'b001: data_out = data_in[1];
                3'b010: data_out = data_in[2];
                3'b011: data_out = data_in[3];
                3'b100: data_out = data_in[4];
                3'b101: data_out = data_in[5];
                3'b110: data_out = data_in[6];
                3'b111: data_out = data_in[7];
            endcase
        end else begin
            data_out = 1'bx;
        end
    end
endmodule



//------------------------------- Testbench -------------------------------//
module tb_mux8to1;
    // Declare testbench signals
    reg [7:0] data_in;   // Input data
    reg [2:0] sel;       // Select signal
    wire data_out;       // Output data

    // Instantiate the DUT 
    mux8to1 uut (
        .data_in(data_in),
        .sel(sel),
        .data_out(data_out)
    );

    // Test stimulus
    initial begin
        //---------------------------------------Test Normal Flow--------------------------------------//
        $display("-------------Test Normal Flow-------------");
        // Test case 1
        data_in = $random % 256; sel = 3'b000; #10;

        // Test case 2
        data_in =  $random % 256; sel = 3'b001; #10;

        // Test case 3
        data_in = $random % 256; sel = 3'b010; #10;

        // Test case 4
        data_in = $random % 256; sel = 3'b011; #10;

        // Test case 5
        data_in = $random % 256; sel = 3'b100; #10;

        // Test case 6
        data_in = $random % 256; sel = 3'b101; #10;

        // Test case 7
        data_in = $random % 256; sel = 3'b110; #10;

        // Test case 8
        data_in = $random % 256; sel = 3'b111; #10;

        //---------------------------------------Test Invalid Flow--------------------------------------//
        $display("-------------Test Invalid Flow-------------");
        // Test case 9
        data_in = $random % 256; sel = 3'b1x1; #10;

        // Test case 10
        data_in = $random % 256; sel = 3'b1zx; #10;

        // Test case 11
        data_in = $random % 256; sel = 3'b1z0; #10;
        $finish;
    end

    // Monitor 
    initial begin
        $monitor("data_in: %b, sel: %b || data_out: %b", data_in, sel, data_out);
    end
endmodule
