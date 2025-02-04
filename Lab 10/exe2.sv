// //----------------------------------------------Detect Sequence----------------------------------------------//
module detect_sequence(
    input clk, rst_n,
    input data_in,
    output valid
);
    localparam  init = 6'b000001,
                S1 = 6'b000010,
                S01 = 6'b000100,
                S101 = 6'b001000,
                S1101 = 6'b010000,
                S01101 = 6'b100000;

    logic [5:0] currentState, nextState;
    
    // State memory
    always_ff @(posedge clk or negedge rst_n) begin : MemoryState
        if(!rst_n) begin
            currentState <= init;
        end
        else begin
            currentState <= nextState;
        end
    end

    // Next State Logic
    always_comb begin : NextState
        case(currentState)
            init: begin
                if(data_in) nextState = S1;
                else nextState = init;
            end
            S1: begin
                if(data_in) nextState = S1;
                else nextState = S01;
            end 
            S01: begin
                if(data_in) nextState = S101;
                else nextState = init;
            end
            S101: begin
                if(data_in) nextState = S1101;
                else nextState = S01;
            end
            S1101: begin
                if(data_in) nextState = S1;
                else nextState = S01101;
            end
            S01101: begin
                nextState = init;
            end
            default: nextState = init;
        endcase
    end

    // Output Logic
    assign valid = (currentState == S01101);
endmodule

//----------------------------------------------Testbench----------------------------------------------//
module detect_sequence_tb;

    // Inputs
    logic clk;
    logic rst_n;
    logic data_in;
    int failed = 0;

    // Outputs
    logic valid;

    // Instantiate the design under test (DUT)
    detect_sequence dut (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .valid(valid)
    );

    // Clock generation
    always #5 clk = ~clk; // 10ns clock period

    // Coverage
  	covergroup c_group @(posedge clk);
      	option.per_instance=1;
        cp_rst: coverpoint rst_n;
      	cp_state: coverpoint dut.currentState{  bins init = {6'b000001};
                                                bins S1 = {6'b000010};
                                                bins S01 = {6'b000100};
                                                bins S101 = {6'b001000};
                                                bins S1101 = {6'b010000};
                                                bins S01101 = {6'b100000};
                                                illegal_bins others = default;}

        cp_transition: coverpoint dut.currentState{ bins Init_to_S1 = (6'b000001 => 6'b000010);
                                                    bins Init_to_Init = (6'b000001 => 6'b000001);
                                                    bins S1_to_S1 = (6'b000010 => 6'b000010);
                                                    bins S1_to_S01 = (6'b000010 => 6'b000100);
                                                    bins S01_to_Init = (6'b000100 => 6'b000001);
                                                    bins S01_to_S101 = (6'b000100 => 6'b001000);
                                                    bins S101_to_S01 = (6'b001000 => 6'b000100);
                                                    bins S101_to_S1101 = (6'b001000 => 6'b010000);
                                                    bins S1101_to_S1 = (6'b010000 => 6'b000010);
                                                    bins S1101_to_S01101 = (6'b010000 => 6'b100000);
                                                    bins S01101_to_Init = (6'b100000 => 6'b000001);
                                                    }
        
    endgroup
  	c_group cg;

     // Test sequence
    initial begin
        // Initialize inputs
        clk = 0;
        rst_n = 0;
        data_in = 0;
        cg = new();
        #10 rst_n = 1;  // Reset to initialize FSM

        // Test Case 1: Sequence "10110" followed by reset
        #10 data_in = 1; // S1
        #10 data_in = 0; // S01
        #10 data_in = 1; // S101
        #10 data_in = 1; // S1101
        #10 data_in = 0; // S01101 - valid = 1
        #10 rst_n = 0;   // Apply reset
        #10 rst_n = 1;   // Reset completed, back to init state

        // Test Case 2: Random Invalid Sequence
        repeat(20) #10 data_in = $urandom % 2; // Random sequence of 0s and 1s

        // Test Case 3: Overlapping Sequence Detection
        #10 data_in = 1; // S1
        #10 data_in = 0; // S01
        #10 data_in = 1; // S101
        #10 data_in = 1; // S1101
        #10 data_in = 0; // S01101 - valid = 1
        #10 data_in = 1; // S1 (start new sequence)
        #10 data_in = 0; // S01 (start new sequence)

        // Test Case 4: Sequence "10110" with invalid bit in the middle
        #10 data_in = 1; // S1
        #10 data_in = 0; // S01
        #10 data_in = 0; // invalid sequence (no valid state transition)
        #10 data_in = 1; // S1 (should restart)

        // Test Case 5: Reset Applied Mid-sequence
        #10 data_in = 1; // S1
        #10 data_in = 0; // S01
        #10 rst_n = 0;   // Apply reset
        #10 rst_n = 1;   // Reset completes, FSM goes to init state
        #10 data_in = 1; // S1 - start new sequence

        // Test Case 6: Long sequence with random inputs
        repeat(50) #10 data_in = $urandom % 2;

        // End simulation
        $finish;
    end

    // Monitor signals
    // initial begin
    //     forever begin
    //         @(posedge clk);
    //         $display("Time=%0t clk=%b rst_n=%b data_in=%b valid=%b state=%b",
    //              $time, clk, rst_n, data_in, valid, dut.currentState);
    //     end
        
    // end

    // Generate waveform
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
        $set_coverage_db_name("test.ucdb"); 
    end

    // Sequences
    sequence valid_state;
        $onehot(dut.currentState) && (dut.currentState == 6'b000001 || dut.currentState == 6'b000010 || dut.currentState == 6'b000100 || dut.currentState == 6'b001000 || dut.currentState == 6'b010000 || dut.currentState == 6'b100000);
    endsequence

    sequence valid_transition;
        (dut.currentState == 6'b000001 && (!data_in && dut.nextState == 6'b000001 || data_in && dut.nextState == 6'b000010)) ||
        (dut.currentState == 6'b000010 && (!data_in && dut.nextState == 6'b000100 || data_in && dut.nextState == 6'b000010)) ||
        (dut.currentState == 6'b000100 && (!data_in && dut.nextState == 6'b000001 || data_in && dut.nextState == 6'b001000)) ||
        (dut.currentState == 6'b001000 && (!data_in && dut.nextState == 6'b000100 || data_in && dut.nextState == 6'b010000)) ||
        (dut.currentState == 6'b010000 && (!data_in && dut.nextState == 6'b100000 || data_in && dut.nextState == 6'b000010)) ||
        (dut.currentState == 6'b100000 && dut.nextState == 6'b000001);
    endsequence

    sequence valid_output;
        dut.currentState == 6'b100000;
    endsequence

    sequence output_duration;
        valid ##1 !valid; 
    endsequence

    // Properties
    property check_valid_state;
        @(posedge clk) valid_state;
    endproperty

    property check_valid_transitions;
        @(posedge clk) valid_transition;
    endproperty

    property check_valid_output;
        @(posedge clk) disable iff(!rst_n) valid |-> valid_output;
    endproperty

    property check_output_duration;
        @(posedge clk) disable iff(!rst_n) valid |-> output_duration;
    endproperty

    // Assertions
    assert property (check_valid_state) begin
        $display("[TIME: %0t][PASSED] Valid State", $time);
    end else begin
        failed++;   
        $error("[TIME: %0t][FAILED] FSM is not in a valid one-hot encoded state!", $time);
    end

    assert property (check_valid_transitions) begin
        $display("[TIME: %0t][PASSED] Valid Transition", $time);
    end else begin
        $error("[TIME: %0t][FAILED] Invalid transition", $time);
    end 

    assert property (check_valid_output) begin
        $display("[TIME: %0t][PASSED] Valid Output State", $time);
    end else begin
        failed++; 
        $error("[TIME: %0t][FAILED] Output valid is high for an incorrect state!", $time);
    end

    assert property (check_output_duration) begin
        $display("[TIME: %0t][PASSED] Valid output duration", $time);
    end else begin
        failed++; 
        $error("[TIME: %0t][FAILED] Output valid is high for more than one cycle!", $time);
    end

    final begin
        if(failed == 0) begin
            $display("===========================");
            $display("ALL PASSED TEST!!!");
            $display("===========================");
        end
        else begin
            $display("===========================");
            $display("TEST FAILED: %d", failed);
            $display("===========================");
        end
        
    end

endmodule
