//------------------------------------ Dynamic array ------------------------------------//
module dynamic_array;
    // Declare dynamic array
    bit [9:0] dynamic_array[];
    int i;
    initial begin
        // Allocate 20 memory location
        $display("-------------Allocate 20 memory location-------------");
        dynamic_array = new[20];
        for(i = 0; i < 20; i = i + 1) begin
            dynamic_array[i] = $random % 256;
        end

        foreach(dynamic_array[i]) begin
            $display("dynamic_array[%0d]: %h", i, dynamic_array[i]);
        end

        $display("-------------Array Size-------------");
        $display("Size of dynamic_array: %0d", dynamic_array.size());

        // Double the size 
        $display("-------------Double the size of array-------------");
      	dynamic_array = new[40](dynamic_array);
       	dynamic_array[32] = $random % 256;
        dynamic_array[23] = $random % 256;
        dynamic_array[35] = $random % 256;
        dynamic_array[27] = $random % 256;
        dynamic_array[20] = $random % 256;
        dynamic_array[21] = $random % 256;
        foreach(dynamic_array[i]) begin
            $display("dynamic_array[%0d]: %h", i, dynamic_array[i]);
        end
        $display("-------------Array Size-------------");
        $display("Size of dynamic_array: %0d", dynamic_array.size());
    end
endmodule