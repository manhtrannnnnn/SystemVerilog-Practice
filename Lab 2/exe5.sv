//----------------------------------- Associative Arrays with index type Springs -----------------------------------//
module associate_array;

    // Declare an associative array with int values and string indices
    int associative_array[string];
    initial begin
        // Assign ASCII values to the associative array
        associative_array = '{
            "0": 48,
            "1": 49,
            "2": 50,
            "3": 51,
            "4": 52,
            "5": 53,
            "6": 54,
            "7": 55,
            "8": 56,
            "9": 57,
            "a": 97,
            "b": 98,
            "c": 99,
            "d": 100,
            "e": 101,
            "f": 102,
            "g": 103,
            "h": 104,
            "P": 80,
            "Q": 81,
            "R": 82,
            "S": 83,
            "T": 84,
            "U": 85,
            "V": 86,
            "W": 87,
            "X": 88,
            "Y": 89,
            "Z": 90
        };

        // Print all value of the associative array
        $display("------------- Print all value of the associative array -------------");
        $display("Associative Array: %p", associative_array);

        // Check the value exists at index "x", "A", "p" and "T"
        $display("------------- Check the value exists at index 'x', 'A', 'p' and 'T' -------------");
        if(associative_array.exists("x")) begin
            $display("Value at index 'x': %d", associative_array["x"]);
        end
        else begin
            $display("Value at index 'x' does not exist");
        end

        if(associative_array.exists("A")) begin
            $display("Value at index 'A': %d", associative_array["A"]);
        end
        else begin
            $display("Value at index 'A' does not exist");
        end

        if(associative_array.exists("p")) begin
            $display("Value at index 'p': %d", associative_array["p"]);
        end
        else begin
            $display("Value at index 'p' does not exist");
        end

        if(associative_array.exists("T")) begin
            $display("Value at index 'T': %d", associative_array["T"]);
        end
        else begin
            $display("Value at index 'T' does not exist");
        end

        // Print num of elements in the associative array
        $display("------------- Print num of elements in the associative array -------------");
        $display("Number of elements in the associative array: %0d", associative_array.size());

        //  Delete first three and last 5 elements
        $display("------------- Delete first 3 and last 5 elements -------------");
        associative_array.delete("0");
        associative_array.delete("1");
        associative_array.delete("2");
        associative_array.delete("V");
        associative_array.delete("W");
        associative_array.delete("X");
        associative_array.delete("Y");
        associative_array.delete("Z");
        $display("Associative Array after deletion: %p", associative_array);
        $display("Number of elements in the associative array after deletion: %0d", associative_array.size());
        $finish;
    end
endmodule
