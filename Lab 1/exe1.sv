//------------------------Output------------------------//
// Default value of single_bit: 0
// Default value of eight_bit: 00000000
// Default value of my8bit_signed: xxxxxxxx
// Default value of sign32bit: 0
// Default value of unsign32bit: x
// Default value of my_byte: 0
// Default value of my_shortint: 0
// Default value of my_longint: 0
// => defaut of 4-state logic is 'x' (unknown) || defaut of 2-state logic is '0' (unknown)



//-------------------------------------arthemetic right shift-------------------------------------//
module right_shift;
    // Bit: 1-bit value
    bit single_bit;

    // 8-bit: Unsigned 8-bit value
    bit [7:0] eight_bit;

    // 8-bit: signed logic
    logic signed [7:0] my8bit_signed;

    // int: 32 signed bit
    int sign32bit;

    // integer: 32 unsigned bit
    integer unsign32bit;

    // byte: 8-bit unsigned value
    byte my_byte;

    // shortint: 16-bit signed value
    shortint my_shortint;

    // longint: 64-bit signed value
    longint my_longint;

    initial begin
        //=================================================
        // Default Value
        //=================================================

        $display("----------------Default value----------------");
        // Print default value of single_bit
        $display("Default value of single_bit: %b", single_bit);
        // Print default value of eight_bit
        $display("Default value of eight_bit: %b", eight_bit);
        // Print default value of my8bit_signed
        $display("Default value of my8bit_signed: %b", my8bit_signed);
        // Print default value of sign32bit
        $display("Default value of sign32bit: %d", sign32bit);
        // Print default value of unsign32bit
        $display("Default value of unsign32bit: %d", unsign32bit);
        // Print default value of my_byte
        $display("Default value of my_byte: %d", my_byte);
        // Print default value of my_shortint
        $display("Default value of my_shortint: %d", my_shortint);
        // Print default value of my_longint
        $display("Default value of my_longint: %d", my_longint);
        #10;
        
        // Default value of single_bit: 0
        // Default value of eight_bit: 00000000
        // Default value of my8bit_signed: xxxxxxxx
        // Default value of sign32bit: 0
        // Default value of unsign32bit: x
        // Default value of my_byte: 0
        // Default value of my_shortint: 0
        // Default value of my_longint: 0
        // => defaut of 4-state logic is 'x' (unknown) || defaut of 2-state logic is '0' (unknown)


        //=================================================
        // Fill 1
        //=================================================

        $display("----------------value after fill 1----------------");
        single_bit = 1'b1;
        eight_bit = 8'b11111111;
        my8bit_signed = 8'b11111111;
        sign32bit = {32{1'b1}};
        unsign32bit = {32{1'b1}};
        my_byte = 8'b11111111;
        my_shortint = {16{1'b1}};
        my_longint = {64{1'b1}};

        // Print value after fill 1 of single_bit
        $display("Single_bit: %d", single_bit);
        // Print value after fill 1 of eight_bit
        $display("Eight_bit: %d", eight_bit);
        // Print value after fill 1 of my8bit_signed
        $display("8 Bit Signed: %d", my8bit_signed);
        // Print value after fill 1 of sign32bit
        $display("Signed 32 bit: %d", sign32bit);
        // Print value after fill 1 of unsign32bit
        $display("Unsigned 32 bit: %d", unsign32bit);
        // Print value after fill 1 of my_byte
        $display("Byte: %d", my_byte);
        // Print value after fill 1 of my_shortint
        $display("Short int: %d", my_shortint);
        // Print value after fill 1 of my_longint
        $display("My long int: %d", my_longint);
        #10;

        //=================================================
        // Shift Right 
        //=================================================
        $display("----------------Value after shift right----------------");
        single_bit = single_bit >>> 5;
        eight_bit = eight_bit >>> 5;
        my8bit_signed = my8bit_signed >>> 5;
        sign32bit = sign32bit >>> 5;
        unsign32bit = unsign32bit >>> 5;
        my_byte = my_byte >>> 5;
        my_shortint = my_shortint >>> 5;
        my_longint = my_longint >>> 5;
        
        // Print value after shift right of single_bit
        $display("Single_bit: %b", single_bit);
        // Print value after shift right of eight_bit
        $display("Eight_bit: %b", eight_bit);
        // Print value after shift right of my8bit_signed
        $display("8 Bit Signed: %b", my8bit_signed);
        // Print value after shift right of sign32bit
        $display("Signed 32 bit: %b", sign32bit);
        // Print value after shift right of unsign32bit
        $display("Unsigned 32 bit: %b", unsign32bit);
        // Print value after shift right of my_byte
        $display("Byte: %b", my_byte);
        // Print value after shift right of my_shortint
        $display("Short int: %b", my_shortint);
        // Print value after shift right of my_longint
        $display("My long int: %b", my_longint);

        // fill with value of sign bit if expression is signed, otherwise fill with zero,


        //=================================================================
        //Assign value 8’b10X1_ZX10 to 8-bit variable and observe the result
        //=================================================================
        $display("----------------Assign value 8’b10X1_ZX10 to 8-bit variable----------------");
        eight_bit = 8'b10X1_ZX10;
        $display("Eight_bit: %b", eight_bit);

        // Eight_bit: 1001_0010 => X, Z turn to 0
        $finish;
    end
endmodule



































