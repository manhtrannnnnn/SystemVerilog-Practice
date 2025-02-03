//-------------------------------------------------Arbiter-------------------------------------------------//
module arbiter(
    input  logic clk, rst_n,
    input  logic req1, req2, req3, req4,
    output logic gnt1, gnt2, gnt3, gnt4 
);
    typedef enum logic [1:0] {IDLE, WAIT, GRANT} state_type;
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
                    gnt1 <= 0;
                    gnt2 <= 0;
                    gnt3 <= 0;
                    gnt4 <= 0;
                    duration_count <= 0;
                    if (req1 | req2 | req3 | req4) begin
                        state <= WAIT;
                        wait_count <= $urandom_range(2, 6);
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
                        duration_count <= 2'b01;  
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
                        duration_count <= $urandom_range(0, 1);
                    end else begin
                        gnt1 <= 0;
                        gnt2 <= 0;
                        gnt3 <= 0;
                        gnt4 <= 0;
                        state <= IDLE;
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

    // Test stimulus
    initial begin
        // Initialize the data 
        rst_n = 0; req1 = 0; req2 = 0; req3 = 0; req4 = 0;
        
        //--------------------Testcase 1--------------------//
        #10; rst_n = 1; req1 = 1; req2 = 1; req3 = 0; req4 = 0;
        #10; req1 = 0;
        #1000; 
        $finish;
    end

    // Waveform
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end


    // Property
    property check_priority;
        @(posedge clk) disable iff(!rst_n && dut.state == 1)
        ((req1 |=> ##[3:7] gnt1) or
        (!req1 && req2 |=> ##[3:7] gnt2) or
        (!req1 && !req2 && req3 |=> ##[3:7] gnt3) or
        (!req1 && !req2 && !req3 && req4 |=> ##[3:7] gnt4));
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

    property check_noreq_during_grant;
        @(posedge clk) 
        $onehot({gnt1, gnt2, gnt3, gnt4}) |-> !(req1 || req2 || req3 || req4) throughout $onehot({gnt1, gnt2, gnt3, gnt4});
    endproperty

    // Assertion
    assert property(check_priority) begin
        $display("[PASSED] Valid Priority");
    end else begin
       $error("[FAILED] Failed Priority"); 
    end

    assert property(check_single_grant) begin
        $display("[PASSED] Valid single grant");
    end else begin
        $error("[FAILED] Failed single grant");
    end

    assert property(check_grant_duration) begin
        $display("[PASSED] Valid grant duration");
    end else begin
        $error("[FAILED] Failed grant duration");
    end

    assert property(check_noreq_during_grant) begin
        $display("[PASSED] Valid No Request during grant");
    end else begin
        $error("[FAILED] Failed No Request during grant");
    end

endmodule