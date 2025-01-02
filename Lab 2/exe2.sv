//-------------------------------------Queue-------------------------------------//
•Declare an integer queue. Initialize it with five elements (0 to 4). Perform following operations on queue and print content after every operation:
•Insert an element (value 19) at beginning without any method.
•Insert an element (value 29) at beginning using predefined method.
•Insert an element (value 39) at the end using predefined method.
•Insert an element (value 49) at index 4.
•Get 1st element in queue and compare with value 29.
•Get last element in queue and compare with value 39.
•Try to get value at index 3 without removing it from queue.
•Delete an element at index 4 in queue.


module queue;
    // Declare integer queue
    int q[$] = {0, 1, 2, 3, 4};
    int tmp;
    initial begin
        // Insert an elenment (value 19) at beginning without any method
        $display("-------------Insert an element (value 19) at beginning without any method-------------");
        for(int i = q.size() - 1; i >= 0; i = i - 1) begin
            q[i + 1] = q[i];
        end
        q[0] = 19;  
        foreach(q[i]) begin
            $display("q[%0d]: %d", i, q[i]);
        end

        // Insert an element (value 29) at beginning using predefined method
        $display("-------------Insert an element (value 29) at beginning using predefined method-------------");
        q.push_front(29);
        foreach(q[i]) begin
            $display("q[%0d]: %d", i, q[i]);
        end

        // Insert an element (value 39) at the end using predefined method
        $display("-------------Insert an element (value 39) at the end using predefined method-------------");
        q.push_back(39);
        foreach(q[i]) begin
            $display("q[%0d]: %d", i, q[i]);
        end

        // Insert an element (value 49) at index 4
        $display("-------------Insert an element (value 49) at index 4-------------");
        q.insert(4, 49);
        foreach(q[i]) begin
            $display("q[%0d]: %d", i, q[i]);
        end

        // Get 1st element in queue and compare with value 29
        $display("-------------Get 1st element in queue and compare with value 29-------------");
        tmp = q.pop_front();
        if(tmp == 29) begin
            $display("The 1st element is 29");
        end
        else begin
            $display("The 1st element is not 29");
        end

        // Get last element in queue and compare with value 39
        $display("-------------Get last element in queue and compare with value 39-------------");
        tmp = q.pop_back();
        if(tmp == 39) begin
            $display("The last element is 39");
        end
        else begin
            $display("The last element is not 39");
        end

        // Try to get value at index 3 without removing it from queue
       $display("-----------------Try to get value at index 3 without removing it from queue-----------------");
        tmp = q[3];
        $display("The value at index 3 is %d", tmp);

        // Delete an element at index 4 in queue
        $display("-------------Delete an element at index 4 in queue-------------");
        q.delete(4);
        foreach(q[i]) begin
            $display("q[%0d]: %d", i, q[i]);
        end
    end
endmodule