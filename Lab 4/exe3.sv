//---------------------------------------------Add function and task to the module---------------------------------------------//
module adder;
    int result;

    function int add(input int a, input int b);
        return a + b;
    endfunction

    task add(input int a, input int b, output int result);
        result = a + b;
    endtask

    initial begin
        result = add(3, 5); // function
        $display("Function result: %0d", result);

        add(4, 6, result); // task
        $display("Task result: %0d", result);
    end
endmodule



// Error: Duplicate identifier: add 



//---------------------------------------------Subprogram Overloading - Package---------------------------------------------//
package my_pkg;

    // Function 
    function int add(input int a, input int b);
        return a + b;
    endfunction

endpackage


module top;
    import my_pkg::add; 
  	int result;

    //Task
    task add(input int a, input int b, output int result);
        result = a + b;
    endtask

    initial begin
        
        // Function
        result = my_pkg::add(3, 5);
        $display("Function result: %0d", result);

        // Task
        add(5,4, result);
        $display("Task result: %0d", result);
    end
endmodule