module packed_array;
    // Declare 2D (4x8) packed array of bits
    bit [3:0][7:0] packed_array; // This is a 32-bit packed array (4 x 8 bits)
    bit [7:0] tmp0, tmp1, tmp2, tmp3;
    bit highestbit, lowestbit;
    bit [7:0] highestpoint, lowestpoint;

    initial begin
        // Initialize the packed array
        packed_array = '{8'hAB, 8'hCF, 8'hDE, 8'hAD};

        // Access full packed array
        $display("-------------Access full packed array-------------");
        $display("packed_array: %p", packed_array);

        // Access specific elements of the packed array 
        tmp0 = packed_array[0];
        tmp1 = packed_array[1];
        tmp2 = packed_array[2];
        tmp3 = packed_array[3];
        $display("tmp0: %h || tmp1: %h || tmp2: %h || tmp3: %h", tmp0, tmp1, tmp2, tmp3);

        // Access significant bits of packed array
        $display("----------------Access significant bits of packed array----------------");
        highestbit = packed_array[3][7];
        $display("Highest bit of packed array: %b", highestbit);

        // Access highest point of packed array
        $display("----------------Access highest point of packed array----------------");
        highestpoint = packed_array[3];
        $display("Highest point of packed array: %h", highestpoint);

        // Access lowest bits of packed array
        $display("----------------Access lowest bits of packed array----------------");
        lowestbit = packed_array[0][0];
        $display("Lowest bit of packed array: %b", lowestbit);

        // Access lowest point of packed array
        $display("----------------Access lowest point of packed array----------------");
        lowestpoint = packed_array[0];
        $display("Lowest point of packed array: %h", lowestpoint);

        $finish;
    end
endmodule
