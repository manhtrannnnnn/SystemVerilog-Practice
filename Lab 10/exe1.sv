//-------------------------------------------------Arbiter-------------------------------------------------//
module arbiter(
    input  logic clk, rst_n,
    input  logic req1, req2, req3, req4,
    output logic gnt1, gnt2, gnt3, gnt4 
);
  typedef enum logic [1:0] {IDLE = 0, WAIT, GRANT} state_type;
    state_type state;

    logic [2:0] wait_count;
    logic [1:0] duration_count;
    logic [1:0] signals;


    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            wait_count <= 0;
            duration_count <= 0;
            gnt1 <= 0;
            gnt2 <= 0;
            gnt3 <= 0;
            gnt4 <= 0;
        end else begin
            case (state)
                IDLE: begin
                    if (req1 | req2 | req3 | req4) begin
                        state <= WAIT;
                        wait_count <= $urandom_range(2,6);
                        if (req1)      signals <= 2'b00;
                        else if (req2) signals <= 2'b01;
                        else if (req3) signals <= 2'b10;
                        else if (req4) signals <= 2'b11;
                    end
                end

                WAIT: begin
                    if (wait_count > 0) begin
                        wait_count <= wait_count - 1;
                    end else begin
                        state <= GRANT;
                      	duration_count <= $urandom_range(0,1);  
                        case (signals)
                            2'b00: gnt1 <= 1;
                            2'b01: gnt2 <= 1;
                            2'b10: gnt3 <= 1;
                            2'b11: gnt4 <= 1;
                        endcase
                    end
                end

                GRANT: begin
                    if (duration_count > 0) begin
                        duration_count <= duration_count - 1;
                    end else begin
                        gnt1 <= 0;
                        gnt2 <= 0;
                        gnt3 <= 0;
                        gnt4 <= 0;
                        if (req1 | req2 | req3 | req4) begin
                          state <= WAIT;
                          wait_count <= $urandom_range(2,6);
                          if (req1)      signals <= 2'b00;
                          else if (req2) signals <= 2'b01;
                          else if (req3) signals <= 2'b10;
                          else if (req4) signals <= 2'b11;
                    	end
                        else begin
                            state <= IDLE;
                        end
                    end
                end
            endcase
        end
    end
endmodule

//-------------------------------------------------Testbench-------------------------------------------------//
module arbiter_tb;
    // Test input
    logic clk, rst_n;
    logic req1, req2, req3, req4;
    // Test output
    logic gnt1, gnt2, gnt3, gnt4;


    // Instantiate DUT
    arbiter dut (
        .clk(clk),
        .rst_n(rst_n),
        .req1(req1), .req2(req2), .req3(req3), .req4(req4),
        .gnt1(gnt1), .gnt2(gnt2), .gnt3(gnt3), .gnt4(gnt4)
    );

    // Clock generate 
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Coverage
    covergroup c_group @(posedge clk);
        option.per_instance=1;
        cp_rst: coverpoint rst_n;
    endgroup

    // Reset sequence
    initial begin
        clk = 0;
        rst_n = 0;
        req1 = 0; req2 = 0; req3 = 0; req4 = 0;
        #10 rst_n = 1;
    end

    // Test scenarios
    initial begin
        #20;
        //-----------------------------Testcase 1: Toggling all request and grants-----------------------------//
        $display("-----------------Testcase 1: Toogle all single request-----------------");
        req1 = 1; #10; req1 = 0;
        #100;
        req2 = 1; #10; req2 = 0;
        #100;
        req3 = 1; #10; req3 = 0;
        #100;
        req4 = 1; #10; req4 = 0;
        #100;

        //-----------------------------Testcase 2: Multiple requests, check priority-----------------------------//
        $display("-----------------Testcase 2: Multiple request for priority-----------------");
        req1 = 1; req2 = 1; #10; // 1 vs 2
        req1 = 0; req2 = 0;
        #100;

        req1 = 1; req3 = 1; #10; // 1 vs 3
        req1 = 0; req3 = 0;
        #100;

        req1 = 1; req4 = 1; #10; // 1 vs 4
        req1 = 0; req4 = 0;
        #100;

        req2 = 1; req3 = 1; #10; // 2 vs 3
        req2 = 0; req3 = 0;
        #100;

        req2 = 1; req4 = 1; #10; // 2 vs 4
        req2 = 0; req4 = 0;
        #100;

        req3 = 1; req4 = 1; #10; // 3 vs 4
        req3 = 0; req4 = 0;
        #100;

        //-----------------------------Test 3: Ensure grant stays high for 1 or 2 cycles-----------------------------//
        $display("-----------------Testcase 3: Grant high for 1 or 2 cycles-----------------");
        req1 = 1; #10; req1 = 0;
        #100;
        req2 = 1; #10; req2 = 0;
        #100;

        // Test 4: Ensure grants are given 3-7 cycles after request
        req3 = 1; #10; req3 = 0;
        #100;
        req4 = 1; #10; req4 = 0;
        #100;

        //-----------------------------Test 5: Request given while grant is still high-----------------------------//
        $display("-----------------Testcase 3: Request given while grant is still high-----------------");
        req1 = 1; #10;
        req1 = 0; req2 = 1; #10;
        req1 = 0; req2 = 0;
        #100;

        req1 = 1; #10;
        req1 = 0; #40;
        req2 = 1; #10;
        req1 = 0; req2 = 0;
        #100;

        // End simulation
        $finish;
    end

    // Waveform
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end

    // Sequence
    sequence priority_req1;
        req1 ##[3:8] gnt1;
    endsequence

    sequence priority_req2;
        req2 && !req1 ##[3:8] gnt2;
    endsequence

    sequence priority_req3;
        req3 && !req1 && !req2 ##[3:8] gnt3;
    endsequence 

    sequence priority_req4;
        req4 && !req1 && !req2 && !req3 ##[3:8] gnt4;
    endsequence

    // Property
    property check_priority_req1;
      @(posedge clk) disable iff(!rst_n) 
            req1 && !$onehot({gnt1, gnt2, gnt3, gnt4}) && dut.state != 1 |-> priority_req1;
    endproperty 

    property check_priority_req2;
      @(posedge clk) disable iff(!rst_n) 
            req2 && !req1 && !$onehot({gnt1, gnt2, gnt3, gnt4}) && dut.state != 1 |-> priority_req2;
    endproperty

    property check_priority_req3;
      @(posedge clk) disable iff(!rst_n) 
            req3 && !req1 && !req2 && !$onehot({gnt1, gnt2, gnt3, gnt4}) && dut.state != 1 |-> priority_req3;
    endproperty

    property check_priority_req4;
      @(posedge clk) disable iff(!rst_n) 
            req4 && !req1 && !req2 && !req3 && !$onehot({gnt1, gnt2, gnt3, gnt4}) && dut.state != 1 |-> priority_req4;
    endproperty
    
    property check_single_grant;
        @(posedge clk) $onehot0({gnt1, gnt2, gnt3, gnt4});
    endproperty

    property check_grant_duration;
        @(posedge clk) disable iff(!rst_n) 
        $onehot({gnt1, gnt2, gnt3, gnt4}) |->
        (gnt1 |=> ##[1:2] !gnt1) and
        (gnt2 |=> ##[1:2] !gnt2) and
        (gnt3 |=> ##[1:2] !gnt3) and
        (gnt4 |=> ##[1:2] !gnt4);
    endproperty

    // Assertion
    assert property(check_priority_req1) begin
        $display("[TIME: %0t][PASSED] Valid Priority For Request 1", $time);
    end else begin
       $error("[TIME: %0t][FAILED] Failed Priority For Request 1", $time); 
    end

    assert property(check_priority_req2) begin
        $display("[TIME: %0t][PASSED] Valid Priority For Request 2", $time);
    end else begin
       $error("[TIME: %0t][FAILED] Failed Priority For Request 2", $time); 
    end

    assert property(check_priority_req3) begin
        $display("[TIME: %0t][PASSED] Valid Priority For Request 3", $time);
    end else begin
       $error("[TIME: %0t][FAILED] Failed Priority For Request 3", $time); 
    end

    assert property(check_priority_req4) begin
        $display("[TIME: %0t][PASSED] Valid Priority For Request 4", $time);
    end else begin
       $error("[TIME: %0t][FAILED] Failed Priority For Request 4", $time); 
    end

    assert property(check_single_grant) begin
        $display("[TIME: %0t][PASSED] Valid single grant", $time);
    end else begin
        $error("[TIME: %0t][FAILED] Failed single grant", $time);
    end

    assert property(check_grant_duration) begin
        $display("[TIME: %0t][PASSED] Valid grant duration", $time);
    end else begin
        $error("[TIME: %0t][FAILED] Failed grant duration", $time);
    end

endmodule










