//---------------------------------------------Add function and task to the module---------------------------------------------

module adder;
    // Declare input and output
    int a, b;
    int sum;
    // Function definition
    function int add(int a, int b);
        return a + b;
    endfunction

    // Task definition
    task add(int a, int b);
        sum  = a + b;
    endtask

    initial begin
        // Call function
        sum = add(5, 10);
        $display("Sum: %0d", sum);
        // Call task 
        add(5, 10); 
        $display("Sum: %0d", sum);     
		$finish;
    end
endmodule


// Error: Duplicate identifier: add 