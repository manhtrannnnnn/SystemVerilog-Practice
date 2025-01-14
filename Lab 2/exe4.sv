//---------------------------------- Associated Array ----------------------------------//
module associate_array;
    // Declares associative array
    bit [7:0] arr[int];
    int i;
    int value;
    randc int a;

    initial begin
        // Assign 50 value to the array
        for(i = 0; i < 50; i++) begin
            arr[a.randomize with {a < 10 && a > 0;}] = $random % 256;
        end

        // Check Value exists at location 3, 23, 75 and 80
        $display("-----------------Check Value exists at location 3, 23, 75 and 80-----------------");
        $display("Value at location 3: %d", arr.exists(3));
        $display("Value at location 23: %d", arr.exists(23));
        $display("Value at location 75: %d", arr.exists(75));
        $display("Value at location 80: %d", arr.exists(80));

        // Print the value at fist value exists along with index number
        $display("-----------------Print the value at fist value exists along with index number-----------------");
        arr.first(value);
        $display("First value exists: %d", value);

        // Print the value at last value exists along with index number
        $display("-----------------Print the value at last value exists along with index number-----------------");
        arr.last(value);
        $display("Last value exists: %d", value);

        // Print the size of array
        $display("-----------------Print the size of array-----------------");
        $display("Size of array: %d", arr.size());

        // Delete element at location 5, 10, 15 and 100
        $display("-----------------Delete element at location 5, 10, 15 and 100-----------------");
        arr.delete(5);
        arr.delete(10);
        arr.delete(15);
        arr.delete(100);
    
        // Print the size of array after deletion
        $display("-----------------Print the size of array after deletion-----------------");
        $display("Size of array: %d", arr.size());
    end

endmodule